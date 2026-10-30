/* eslint-disable no-console */
'use strict';

/**
 * ============================================================================
 *  GRANDMASTER — full-stack online chess platform (single-file application)
 * ============================================================================
 *  Everything application-specific lives in this one file:
 *    - Express app + HTTP server + Socket.IO server
 *    - Mongoose schemas / models (User, Game, Invitation, RatingHistory, Notification)
 *    - Session authentication (express-session + connect-mongo, shared with Socket.IO)
 *    - REST API, real-time multiplayer, matchmaking, invitations, notifications
 *    - Server-authoritative chess rules (chess.js) + capture-based rating economy
 *    - Legal-move AI engine (three difficulties)
 *    - Embedded HTML / CSS / browser JavaScript (served from this file)
 *
 *  Runtime configuration files (package.json, .env) are the only external files.
 * ============================================================================
 */

/* ---------------------------------------------------------------------------
 * SECTION 1 — ENVIRONMENT & GLOBAL CONSTANTS
 * ------------------------------------------------------------------------- */

require('dotenv').config();

const http = require('http');
const crypto = require('crypto');
const dns = require('dns');
const mongoose = require('mongoose');
const express = require('express');
const session = require('express-session');
/* connect-mongo ships different export shapes across majors (v4 class export,
 * v5/v6 named `MongoStore`). Resolve all of them so either installs work. */
const connectMongoModule = require('connect-mongo');
const MongoStore = connectMongoModule.MongoStore || connectMongoModule.default || connectMongoModule;
const bcrypt = require('bcryptjs');
const helmet = require('helmet');
const rateLimit = require('express-rate-limit');
const { Chess } = require('chess.js');
const { Server: SocketServer } = require('socket.io');

/* Some Windows/ISP resolvers return AAAA records first and Node then fails the
 * TCP connect to Atlas; preferring IPv4 avoids that class of failure. */
try {
  dns.setDefaultResultOrder('ipv4first');
} catch (err) {
  /* Node < 17 has no ordering option — nothing to do. */
}

const NODE_ENV = process.env.NODE_ENV || 'development';
const IS_PROD = NODE_ENV === 'production';
const PORT = process.env.PORT || 3000;
/* Public origin used in logs and any absolute link we ever emit. Set
 * PRODUCTION_URL (or APP_URL / PUBLIC_URL) on the host; the app itself always
 * works with relative URLs, so an unset value is not fatal. */
const PUBLIC_URL = String(process.env.PRODUCTION_URL || process.env.APP_URL || process.env.PUBLIC_URL || '')
  .trim()
  .replace(/\/+$/, '');
const MONGO_URI = (process.env.MONGO_URI || '').trim();
const DB_NAME = process.env.MONGO_DB_NAME || 'chessgame';

/* Session secret: required in production. In development a random per-process
 * secret is generated so `npm start` works immediately (sessions then end on
 * restart, which is the safe behaviour for a throwaway secret). */
const EPHEMERAL_SECRET = !process.env.SESSION_SECRET;
const SESSION_SECRET = EPHEMERAL_SECRET
  ? IS_PROD
    ? ''
    : crypto.randomBytes(48).toString('hex')
  : process.env.SESSION_SECRET;

/* Starting rating for every account. */
const START_RATING = 500;
/* ---- Penalty & clock economy (all configurable via .env) ------------------
 * DECLINE_PENALTY  : points the INVITED player loses when they decline an
 *                    invitation (the inviter is never charged).
 * FORFEIT_PENALTY  : points a player loses for leaving/forfeiting a live PvP
 *                    match. PvAI games carry no penalty.
 * PVP_MATCH_SECONDS: total duration of a live PvP match; when it expires the
 *                    result is decided on captured material.
 * FORFEIT_AWARDED  : whether the 10-point forfeit penalty is transferred to the
 *                    opponent (true) or simply deducted (false, the default).
 * ------------------------------------------------------------------------ */
const DECLINE_PENALTY = Math.max(0, Number(process.env.INVITE_DECLINE_PENALTY ?? 10));
const FORFEIT_PENALTY = Math.max(0, Number(process.env.FORFEIT_PENALTY ?? 10));
const PVP_MATCH_SECONDS = Math.max(30, Number(process.env.PVP_MATCH_SECONDS ?? 600));
const FORFEIT_AWARDED = String(process.env.FORFEIT_AWARDED ?? 'false').toLowerCase() === 'true';
/* Invitation lifetime (ms). Configurable: INVITE_TTL_MINUTES */
const INVITE_TTL_MS = Math.max(1, Number(process.env.INVITE_TTL_MINUTES || 5)) * 60 * 1000;
/* Session lifetime (ms). Configurable: SESSION_TTL_HOURS */
const SESSION_TTL_MS = Math.max(1, Number(process.env.SESSION_TTL_HOURS || 72)) * 60 * 60 * 1000;
/* AI games never affect ratings unless explicitly enabled below. */
const AI_GAMES_AFFECT_RATING = String(process.env.AI_GAMES_AFFECT_RATING || 'false').toLowerCase() === 'true';
/* Optional external coach (Groq). Only used server-side; never sent to browsers. */
const GROQ_API_KEY = (process.env.GROQ_API_KEY || '').trim();
const GROQ_MODEL = process.env.GROQ_MODEL || 'llama-3.3-70b-versatile';

/* Capture values — EXACT table required by the product spec. */
const PIECE_VALUES = Object.freeze({ p: 1, b: 2, n: 3, r: 4, q: 5, k: 0 });
const PIECE_NAMES = Object.freeze({ p: 'pawn', n: 'knight', b: 'bishop', r: 'rook', q: 'queen', k: 'king' });

const AI_DIFFICULTIES = Object.freeze({
  easy: { label: 'Easy', depth: 1, blunder: 0.35 },
  medium: { label: 'Medium', depth: 2, blunder: 0.12 },
  hard: { label: 'Hard', depth: 3, blunder: 0.0 },
});

/* Bounded, non-blocking logging helper (never logs secrets). */
function log(...args) {
  console.log(`[${new Date().toISOString()}]`, ...args);
}
function logError(context, err) {
  const safe = err && err.message ? err.message : String(err);
  console.error(`[${new Date().toISOString()}] [error] ${context}: ${safe}`);
}
function warn(message) {
  console.warn(`[${new Date().toISOString()}] [warn] ${message}`);
}

/* ---------------------------------------------------------------------------
 * SECTION 2 — PIECE ARTWORK
 * The original Grandmaster "Islamic chess set" vector artwork is preserved
 * verbatim: every path, control point and layering order is the supplied art.
 * White/black variants only differ by palette + gradient stops, so the paths
 * are stored once and re-coloured per side (identical output to the originals).
 * ------------------------------------------------------------------------- */

const PIECE_PALETTES = {
  w: {
    label: 'White',
    body: ['#fffdf3', '#fffdf3', '#b7b1a4'],
    light: ['#fffef7', '#fffef7', '#ddd8ca'],
    metal: ['#f1e1b7', '#f1e1b7', '#ad966d'],
    skin: ['#ead8c1', '#ead8c1', '#a88e79'],
    dark: '#5d5550',
    edge: '#453c36',
    shadow: '#453c36',
    crease: '#978f83',
    goldline: '#8c7459',
    ink: '#453c36',
    shine: '#ffffff',
  },
  b: {
    label: 'Black',
    body: ['#69747a', '#69747a', '#262c32'],
    light: ['#849096', '#849096', '#343d43'],
    metal: ['#c2a477', '#c2a477', '#66523e'],
    skin: ['#b39980', '#b39980', '#6c5c50'],
    dark: '#171b20',
    edge: '#131518',
    shadow: '#131518',
    crease: '#a1a5a1',
    goldline: '#dbc18e',
    ink: '#131518',
    shine: '#c7d2d3',
  },
};

const PEDESTAL_ART = `
 <path class="edge metal" d="M280 828 Q285 802 323 791 L677 791 Q715 802 720 828 L741 846 Q750 855 749 877 L746 893 Q744 911 721 920 L279 920 Q256 911 254 893 L251 877 Q250 855 259 846Z"/>
 <path class="edge body" d="M288 824 Q294 809 324 805 H676 Q706 809 712 824 L711 844 Q684 854 500 855 Q316 854 289 844Z"/>
 <path class="fine shine" d="M306 820 Q500 830 694 820"/>
 <path class="edge dark" d="M267 852 Q500 873 733 852 L738 879 Q500 900 262 879Z"/>
 <path class="fine goldline" d="M278 862 Q500 882 722 862 M274 875 Q500 895 726 875"/>
 <path class="fine goldline" d="M302 869 l9 -7 9 8 -9 7z M357 873 l9 -7 9 8 -9 7z M412 876 l9 -7 9 8 -9 7z M467 878 l9 -7 9 8 -9 7z M522 878 l9 -7 9 8 -9 7z M577 876 l9 -7 9 8 -9 7z M632 873 l9 -7 9 8 -9 7z M687 869 l9 -7 9 8 -9 7z"/>
 <path class="edge metal" d="M257 886 Q500 907 743 886 L739 899 Q735 908 721 912 H279 Q265 908 261 899Z"/>
 <path class="fine shine" d="M282 904 H718"/>`;

const PIECE_ART = {
  p: {
    id: 'soldier',
    transform: 'translate(0 28)',
    art: `
 <path class="edge dark" d="M427 538 L490 539 L486 711 L467 756 H394 Q389 746 403 729 L416 694Z M510 539 L573 538 L584 694 L597 729 Q611 746 606 756 H533 L514 711Z"/>
 <path class="edge body" d="M431 564 L477 568 L472 698 L459 730 H415 L426 694Z M523 568 L569 564 L574 694 L585 730 H541 L528 698Z"/>
 <path class="edge metal" d="M407 717 Q437 725 468 717 L469 743 Q463 754 448 758 H393 Q389 746 403 729Z M532 717 Q563 725 593 717 L597 729 Q611 746 607 758 H552 Q537 754 531 743Z"/>
 <path class="edge body" d="M425 350 Q382 352 358 387 L325 485 L315 579 Q314 602 337 609 Q357 612 364 588 L389 498 L407 468 L407 605 Q500 628 593 605 V468 L611 498 L636 588 Q643 612 663 609 Q686 602 685 579 L675 485 L642 387 Q618 352 575 350Z"/>
 <path class="shadow" d="M381 432 Q390 480 384 522 L365 583 L350 588 L362 502Z M619 432 Q610 480 616 522 L635 583 L650 588 L638 502Z"/>
 <path class="edge dark" d="M421 357 Q445 346 500 354 Q555 346 579 357 L596 399 L580 496 Q500 511 420 496 L404 399Z"/>
 <path class="edge metal" d="M429 369 Q450 361 500 368 Q550 361 571 369 L582 404 L570 482 Q500 496 430 482 L418 404Z"/>
 <path class="fine crease" d="M441 389 V470 M559 389 V470 M458 388 H542 M456 414 H544 M454 440 H546 M452 466 H548"/>
 <path class="edge metal" d="M407 508 Q500 524 593 508 L594 538 Q500 554 406 538Z"/><path class="fine goldline" d="M416 519 Q500 535 584 519"/><path class="edge dark" d="M489 516 h22 v22 h-22z"/>
 <path class="fine crease" d="M431 555 Q444 585 432 609 M469 557 Q475 587 470 615 M531 557 Q525 587 530 615 M569 555 Q556 585 568 609"/>
 <path class="edge dark" d="M626 468 Q658 450 691 468 V540 Q687 581 659 603 Q631 581 627 540Z"/>
 <path class="edge metal" d="M636 476 Q659 464 681 476 V539 Q678 570 659 590 Q640 570 637 539Z"/><path class="fine goldline" d="M645 482 Q659 475 674 482 V535 Q671 560 659 576 Q647 560 644 535Z"/><circle class="edge dark" cx="659" cy="523" r="10"/>
 <path class="edge skin" d="M446 252 Q448 223 469 211 Q500 198 531 211 Q552 223 554 252 L549 299 Q542 325 500 341 Q458 325 451 299Z"/>
 <path class="edge dark" d="M452 290 Q466 302 478 303 Q500 293 522 303 Q534 302 548 290 Q543 321 500 341 Q457 321 452 290Z"/>
 <path class="fine ink" d="M464 263 q9 -5 18 0 M518 263 q9 -5 18 0 M497 268 l-2 13 h10"/>
 <path class="edge metal" d="M428 248 Q426 209 445 182 Q466 154 500 143 Q534 154 555 182 Q574 209 572 248 Q500 263 428 248Z"/>
 <path class="edge body" d="M431 221 Q444 186 470 174 Q500 158 530 174 Q556 186 569 221 Q500 207 431 221Z"/>
 <path class="fine crease" d="M444 210 Q500 183 556 210 M458 190 Q500 173 542 190"/>
 <path class="edge dark" d="M428 229 Q500 244 572 229 L572 249 Q500 266 428 249Z"/><path class="fine goldline" d="M439 240 Q500 253 561 240"/>`,
  },
  n: {
    id: 'horse',
    transform: 'translate(0 10)',
    art: `
 <path class="edge dark" d="M486 214 Q562 185 607 224 Q680 260 686 338 Q729 369 714 426 Q742 471 706 519 Q722 571 685 611 Q690 681 652 776 H351 Q383 705 390 643 Q400 584 429 535 Q453 489 453 436Z"/>
 <path class="edge metal" d="M526 228 Q615 215 646 279 Q597 251 562 269 Q646 268 670 335 Q623 305 577 321 Q668 321 688 385 Q638 356 590 372 Q676 377 696 433 Q646 410 600 421 Q671 438 682 489 Q641 466 602 478 Q661 501 670 548 Q627 527 591 538 Q644 566 645 610 Q611 588 576 605 Q615 641 607 684 L550 715Z"/>
 <path class="fine goldline" d="M557 240 Q625 236 650 285 M573 294 Q633 289 666 341 M583 346 Q650 347 681 390 M598 399 Q660 403 688 438 M605 454 Q660 462 677 493 M602 512 Q643 521 665 551 M588 569 Q622 584 639 612"/>
 <path class="edge body" d="M452 249 Q427 202 439 146 Q468 158 489 196 L509 207 Q521 157 546 143 Q560 185 545 235 Q571 267 574 322 Q574 381 540 432 Q529 450 540 484 Q563 569 600 665 L650 777 L345 777 Q366 718 383 659 Q400 594 426 551 Q451 507 454 452 Q450 428 430 416 Q389 395 355 405 L315 420 Q291 425 269 406 L242 374 Q233 361 248 345 Q282 310 314 276 Q347 241 389 242 L422 248Z"/>
 <path class="shadow" d="M512 416 Q486 457 494 510 Q501 607 448 767 H395 Q436 650 450 575 Q474 489 459 444Z"/>
 <path class="light" d="M315 292 Q346 258 388 256 Q424 258 448 270 Q415 281 394 312 Q365 343 312 350 L271 363 Q291 323 315 292Z"/>
 <path class="fine crease" d="M449 165 Q449 204 468 230 M544 161 Q533 193 530 214 M385 275 Q409 267 434 279 M345 385 Q375 370 404 382 Q423 392 438 407 M477 454 Q478 510 455 551 M477 578 Q460 665 430 743"/>
 <path class="edge dark" d="M407 305 Q421 296 434 302 Q429 318 414 318 Q406 314 407 305Z"/><circle class="shine" cx="422" cy="306" r="4"/>
 <path class="edge dark" d="M282 361 q18 -12 29 -4 q-3 13 -21 17z"/><path class="fine crease" d="M263 392 Q283 400 304 390 M319 373 Q338 359 355 359"/>
 <path class="edge metal" d="M435 251 Q446 258 455 268 Q430 305 421 353 Q412 387 426 418 L406 410 Q396 384 404 346 Q412 294 435 251Z"/>
 <path class="edge metal" d="M314 282 Q329 276 339 277 Q352 320 379 348 Q391 359 410 365 L405 383 Q377 376 362 359 Q330 328 314 282Z"/>
 <path class="fine goldline" d="M324 284 Q337 326 369 355 Q386 371 405 375 M445 264 Q421 308 413 354"/>
 <circle class="edge metal" cx="413" cy="377" r="13"/><circle class="dark" cx="413" cy="377" r="5"/>
 <path class="edge metal" d="M411 390 Q442 440 465 463 Q502 500 547 506 L553 526 Q496 521 452 477 Q427 453 397 401Z"/>
 <path class="fine goldline" d="M410 399 Q440 449 461 469 Q502 510 545 515"/>
 <path class="edge metal" d="M386 687 Q495 707 615 682 L630 731 Q498 755 371 733Z"/><path class="fine goldline" d="M386 707 Q496 727 615 703 M382 722 Q496 742 621 718"/>`,
  },
  b: {
    id: 'camel',
    transform: 'translate(0 12)',
    art: `
 <path class="edge dark" d="M365 603 Q382 593 403 600 L399 688 L388 759 Q381 776 353 776 H326 Q322 762 341 749 L347 682Z M573 593 Q594 589 608 602 L618 680 L635 751 Q657 759 657 775 H607 Q592 770 590 751 L568 675Z"/>
 <path class="edge body" d="M339 462 Q370 432 412 427 Q437 368 466 351 Q489 343 512 386 Q529 414 550 427 Q601 429 628 455 Q648 480 646 526 Q645 575 609 611 Q568 633 490 626 L403 616 Q360 605 337 577 Q317 548 319 513Z"/>
 <path class="shadow" d="M338 540 Q381 573 450 572 Q557 593 633 547 Q621 602 594 611 Q502 632 402 611 Q360 602 338 573Z"/>
 <path class="fine crease" d="M425 426 Q451 390 470 376 Q488 373 506 409 M355 556 Q389 584 427 584 M594 555 Q612 548 628 533"/>
 <path class="edge body" d="M349 497 Q326 472 316 429 Q307 391 298 356 Q288 330 265 321 L240 318 Q220 325 204 314 L188 299 Q179 288 188 276 L206 266 Q222 246 240 237 Q253 231 270 237 L276 203 Q280 184 292 177 Q300 194 299 218 L308 234 Q320 211 333 208 Q338 233 327 253 Q338 275 337 301 Q338 338 353 365 Q370 395 400 427 Q394 463 375 488Z"/>
 <path class="light" d="M295 270 Q310 292 310 326 Q310 377 337 421 Q345 436 361 449 L346 466 Q326 440 316 402 Q304 349 295 324 Q282 302 261 301 Q281 294 295 270Z"/>
 <path class="fine crease" d="M210 286 Q225 278 239 282 M193 302 Q210 307 222 300 M276 242 Q288 250 295 260 M320 344 Q330 387 352 416 M282 194 l4 31 M329 222 l-7 20"/>
 <path class="edge dark" d="M258 258 Q267 251 278 257 Q274 270 263 269Z"/><circle class="shine" cx="268" cy="258" r="3"/>
 <path class="edge body" d="M377 567 Q394 573 409 591 L403 677 L392 749 Q411 760 408 775 H356 Q343 773 344 757 L354 675 L346 608Z M551 585 Q574 578 590 590 L586 674 L601 749 Q620 758 618 775 H570 Q555 771 555 751 L540 676Z"/>
 <path class="fine crease" d="M368 612 L370 673 L360 748 M568 612 L560 674 L573 748"/>
 <path class="edge dark" d="M402 433 Q481 412 557 431 L582 543 Q503 575 412 548Z"/>
 <path class="edge metal" d="M414 444 Q485 426 546 443 L566 531 Q500 555 423 538Z"/>
 <path class="edge body" d="M429 455 Q483 441 534 454 L548 519 Q496 539 436 527Z"/>
 <path class="fine goldline" d="M438 463 Q485 452 526 462 M443 516 Q497 526 539 509 M454 474 l13 12 13 -12 13 12 13 -12 13 12 13 -12 M459 501 l13 -12 13 12 13 -12 13 12 13 -12"/>
 <path class="edge metal" d="M448 426 Q463 405 479 401 Q497 401 510 426 L518 438 Q482 433 441 440Z"/>
 <path class="edge dark" d="M474 548 Q487 552 501 551 L500 623 L479 623Z"/><path class="fine goldline" d="M484 556 V615 M494 556 V615"/>
 <path class="edge metal" d="M241 241 Q251 241 258 245 Q245 267 244 287 Q250 310 271 314 L266 326 Q236 319 230 290 Q230 267 241 241Z"/>
 <path class="fine goldline" d="M238 289 Q252 302 272 297 M271 321 Q311 351 337 391 Q355 424 390 440"/><circle class="edge metal" cx="265" cy="311" r="9"/>`,
  },
  r: {
    id: 'mosque',
    transform: 'translate(0 0)',
    art: `
 <path class="edge dark" d="M270 760 V355 L254 355 L263 324 L263 247 Q270 225 282 215 Q294 225 301 247 V324 L310 355 H294 V760Z M706 760 V355 H690 L699 324 V247 Q706 225 718 215 Q730 225 737 247 V324 L746 355 H730 V760Z"/>
 <path class="edge metal" d="M263 344 H301 V362 H263Z M699 344 H737 V362 H699Z M267 392 H297 V406 H267Z M703 392 H733 V406 H703Z"/>
 <path class="fine goldline" d="M282 375 V726 M718 375 V726 M272 252 Q282 238 292 252 M708 252 Q718 238 728 252"/>
 <path class="edge body" d="M301 471 Q306 422 350 399 Q394 422 399 471Z M601 471 Q606 422 650 399 Q694 422 699 471Z"/><path class="edge metal" d="M291 469 H409 V490 H291Z M591 469 H709 V490 H591Z"/>
 <path class="edge metal" d="M489 202 V165 Q469 154 477 135 Q480 150 495 149 Q507 146 503 132 Q520 145 510 160 L510 202Z"/>
 <path class="edge dark" d="M359 373 Q360 300 408 263 Q440 238 500 204 Q560 238 592 263 Q640 300 641 373Z"/>
 <path class="edge body" d="M373 365 Q375 307 416 274 Q452 245 500 219 Q548 245 584 274 Q625 307 627 365Z"/>
 <path class="fine crease" d="M500 224 Q449 284 453 362 M500 224 Q551 284 547 362 M500 224 V361 M500 224 Q413 284 410 362 M500 224 Q587 284 590 362"/>
 <path class="edge metal" d="M350 364 H650 L661 382 L653 400 H347 L339 382Z"/><path class="fine goldline" d="M358 378 H642 M358 389 H642"/>
 <path class="edge body" d="M324 400 H676 V761 H324Z"/><path class="edge metal" d="M312 405 H688 V428 H312Z M309 734 H691 V756 H309Z M298 756 H702 V787 H298Z"/>
 <path class="edge dark" d="M405 735 V572 Q405 507 500 459 Q595 507 595 572 V735Z"/>
 <path class="edge metal" d="M419 735 V574 Q419 521 500 476 Q581 521 581 574 V735 H565 V577 Q565 531 500 496 Q435 531 435 577 V735Z"/>
 <path class="edge light" d="M448 735 V582 Q448 548 500 519 Q552 548 552 582 V735Z"/>
 <path class="fine crease" d="M500 521 V735 M452 614 H548 M452 660 H548 M452 706 H548"/>
 <path class="fine goldline" d="M463 605 l18 -18 19 18 19 -18 18 18 M463 650 l18 -18 19 18 19 -18 18 18 M463 696 l18 -18 19 18 19 -18 18 18"/>
 <path class="edge dark" d="M344 678 V552 Q344 525 369 508 Q394 525 394 552 V678Z M606 678 V552 Q606 525 631 508 Q656 525 656 552 V678Z"/>
 <path class="fine goldline" d="M350 555 H388 M350 581 H388 M350 607 H388 M350 633 H388 M350 659 H388 M369 529 V670 M612 555 H650 M612 581 H650 M612 607 H650 M612 633 H650 M612 659 H650 M631 529 V670"/>
 <path class="edge metal" d="M329 445 H671 V463 H329Z"/><path class="fine goldline" d="M345 454 h310 M330 744 h340 M316 770 h368"/>`,
  },
  q: {
    id: 'queen',
    transform: 'translate(0 0)',
    art: `
 <path class="edge dark" d="M425 329 Q369 347 342 404 Q318 462 308 575 L271 727 Q269 747 299 754 L330 751 L312 786 Q500 814 688 786 L670 751 L701 754 Q731 747 729 727 L692 575 Q682 462 658 404 Q631 347 575 329Z"/>
 <path class="edge body" d="M426 346 Q373 361 355 417 L321 580 L294 721 Q302 729 320 730 L371 535 L344 772 Q500 794 656 772 L629 535 L680 730 Q698 729 706 721 L679 580 L645 417 Q627 361 574 346Z"/>
 <path class="edge light" d="M432 371 Q500 406 568 371 Q588 430 583 502 L609 774 Q500 790 391 774 L417 502 Q412 430 432 371Z"/>
 <path class="shadow" d="M415 495 Q428 609 399 769 L431 774 Q450 607 444 491Z M585 495 Q572 609 601 769 L569 774 Q550 607 556 491Z"/>
 <path class="fine crease" d="M463 486 Q472 619 454 754 M492 497 Q498 626 490 760 M526 492 Q518 625 534 759 M553 486 Q542 618 567 752"/>
 <path class="edge metal" d="M411 502 Q500 519 589 502 L590 528 Q500 545 410 528Z"/><path class="fine goldline" d="M422 514 Q500 527 578 514"/><path class="edge dark" d="M500 502 l16 15 -16 15 -16 -15z"/>
 <path class="edge metal" d="M329 732 Q500 754 671 732 L668 765 Q500 789 332 765Z"/><path class="fine goldline" d="M345 744 Q500 765 655 744 M347 755 Q500 778 653 755"/>
 <path class="edge dark" d="M405 205 Q405 146 448 120 Q500 95 552 120 Q595 146 595 205 L606 318 Q617 366 590 421 Q551 442 500 466 Q449 442 410 421 Q383 366 394 318Z"/>
 <path class="edge body" d="M416 207 Q416 152 454 132 Q500 110 546 132 Q584 152 584 207 L588 301 Q592 344 572 377 Q544 408 500 429 Q456 408 428 377 Q408 344 412 301Z"/>
 <path class="edge skin" d="M451 205 Q453 175 472 161 Q500 148 528 161 Q547 175 549 205 L545 263 Q537 296 500 312 Q463 296 455 263Z"/>
 <path class="edge light" d="M423 194 Q426 151 459 137 Q501 119 542 138 Q573 151 577 194 Q550 181 539 178 Q525 155 500 156 Q475 155 461 178 Q450 181 423 194Z"/>
 <path class="fine crease" d="M432 174 Q467 142 501 145 Q537 142 568 174 M420 205 Q432 191 450 187 M580 205 Q568 191 550 187"/>
 <path class="edge light" d="M415 237 Q423 283 449 312 Q469 334 500 344 Q535 332 553 310 Q578 283 585 237 L583 295 Q573 347 544 368 Q526 382 500 393 Q474 382 456 368 Q427 347 417 295Z"/>
 <path class="fine crease" d="M426 278 Q440 331 500 360 Q560 331 574 278 M437 319 Q458 358 500 375 Q542 358 563 319"/>
 <path class="fine ink" d="M465 220 q10 -6 20 0 M515 220 q10 -6 20 0 M497 225 l-2 18 q5 3 10 0 M486 258 q14 5 28 0"/>
 <path class="edge metal" d="M490 120 Q482 101 500 81 Q518 101 510 120 L500 134Z"/><path class="fine goldline" d="M500 94 v26"/>`,
  },
  k: {
    id: 'imam',
    transform: 'translate(0 0)',
    art: `
 <path class="edge dark" d="M427 342 Q366 345 337 390 Q304 445 298 550 L257 708 Q253 732 279 746 L328 753 L315 787 Q500 814 685 787 L673 753 L721 746 Q747 732 743 708 L702 550 Q696 445 663 390 Q634 345 573 342Z"/>
 <path class="edge body" d="M420 353 Q370 361 350 404 L310 589 L282 708 Q292 721 320 721 L367 548 L345 773 Q500 795 655 773 L633 548 L680 721 Q708 721 718 708 L690 589 L650 404 Q630 361 580 353Z"/>
 <path class="shadow" d="M365 461 Q385 560 346 771 L397 778 Q420 630 431 508Z M635 461 Q615 560 654 771 L603 778 Q580 630 569 508Z"/>
 <path class="edge light" d="M431 351 Q449 372 500 401 Q551 372 569 351 L605 393 Q580 499 602 776 Q500 790 398 776 Q420 499 395 393Z"/>
 <path class="fine crease" d="M446 457 Q456 585 433 747 M479 480 Q485 612 472 752 M524 480 Q515 620 529 754 M555 454 Q546 592 568 747"/>
 <path class="edge metal" d="M395 389 Q409 376 429 365 Q450 392 500 414 Q550 392 571 365 Q591 376 605 389 Q579 430 500 461 Q421 430 395 389Z"/>
 <path class="fine goldline" d="M408 390 Q450 427 500 445 Q550 427 592 390 M417 400 l8 -3 2 9 M583 400 l-8 -3 -2 9"/>
 <path class="edge metal" d="M396 510 Q500 523 604 510 L606 546 Q500 561 394 546Z"/><path class="fine goldline" d="M403 521 Q500 534 597 521 M403 537 Q500 550 597 537"/><path class="edge dark" d="M483 515 h34 l8 15 -8 15 h-34 l-8 -15z"/><path class="fine goldline" d="M500 520 l9 10 -9 10 -9 -10z"/>
 <path class="edge metal" d="M330 729 Q500 752 670 729 L667 766 Q500 790 333 766Z"/><path class="fine goldline" d="M342 744 Q500 766 658 744 M347 756 Q500 778 653 756"/>
 <path class="edge skin" d="M438 226 Q435 194 456 178 Q500 158 544 178 Q565 194 562 226 L554 282 Q548 314 527 331 L500 341 L473 331 Q452 314 446 282Z"/>
 <path class="edge dark" d="M444 263 Q455 278 470 282 Q500 271 530 282 Q545 278 556 263 Q558 300 545 328 Q531 354 500 374 Q469 354 455 328 Q442 300 444 263Z"/>
 <path class="fine crease" d="M460 287 Q459 320 485 348 M480 290 Q476 322 495 353 M520 290 Q524 322 505 353 M540 287 Q541 320 515 348"/>
 <path class="fine ink" d="M460 233 q12 -7 23 0 M517 233 q12 -7 23 0 M495 238 l-3 19 q8 4 16 0 M480 269 q20 7 40 0"/>
 <path class="edge metal" d="M415 219 Q407 189 422 160 Q437 129 465 124 Q500 108 535 124 Q563 129 578 160 Q593 189 585 219 Q500 240 415 219Z"/>
 <path class="edge light" d="M419 191 Q425 154 460 139 Q499 120 542 140 Q574 154 581 191 Q530 178 500 202 Q470 178 419 191Z"/>
 <path class="fine crease" d="M429 178 Q457 146 501 161 Q537 171 568 164 M435 155 Q472 131 518 146 M420 202 Q463 190 500 211 Q537 190 580 202"/>
 <path class="edge metal" d="M426 209 Q500 224 574 209 L571 228 Q500 245 429 228Z"/><path class="fine goldline" d="M437 218 Q500 232 563 218"/>
 <path class="edge metal" d="M490 124 Q482 104 500 85 Q518 104 510 124 L500 135Z"/><circle class="dark" cx="500" cy="111" r="4"/>`,
  },
};

/**
 * Build a complete standalone SVG document for one piece.
 * Shared by the server (for /api/pieces.svg) and inlined into the browser bundle.
 * NOTE: the generator itself is tiny; the artwork above is the supplied original.
 */
function buildPieceSvg(color, type) {
  const pal = PIECE_PALETTES[color];
  const art = PIECE_ART[type];
  if (!pal || !art) return '';
  const grad = (id, stops) =>
    `<linearGradient id="${id}" x1="0" y1="0" x2="1" y2="1">` +
    `<stop stop-color="${stops[0]}"/><stop offset=".52" stop-color="${stops[1]}"/>` +
    `<stop offset="1" stop-color="${stops[2]}"/></linearGradient>`;
  const title = `${pal.label} ${PIECE_NAMES[type]} — Grandmaster Islamic chess set`;
  return (
    `<svg xmlns="http://www.w3.org/2000/svg" width="1000" height="1000" viewBox="0 0 1000 1000" role="img" aria-label="${title}">` +
    `<title>${title}</title><defs>` +
    grad('gm-body', pal.body) +
    grad('gm-light', pal.light) +
    grad('gm-metal', pal.metal) +
    grad('gm-skin', pal.skin) +
    `<style>` +
    `.edge{stroke:${pal.edge};stroke-width:9;stroke-linejoin:round;stroke-linecap:round} ` +
    `.fine{fill:none;stroke-width:5;stroke-linecap:round;stroke-linejoin:round} ` +
    `.body{fill:url(#gm-body)} .light{fill:url(#gm-light)} .metal{fill:url(#gm-metal)} .skin{fill:url(#gm-skin)} ` +
    `.dark{fill:${pal.dark}} .shadow{fill:${pal.shadow};opacity:.17} .crease{stroke:${pal.crease}} ` +
    `.goldline{stroke:${pal.goldline}} .ink{stroke:${pal.ink}} .shine{stroke:${pal.shine};fill:${pal.shine}}` +
    `</style></defs>` +
    `<g transform="${art.transform}"><g id="${art.id}">${art.art}</g></g>` +
    `<g id="pedestal">${PEDESTAL_ART}</g>` +
    `</svg>`
  );
}

/* ---------------------------------------------------------------------------
 * SECTION 3 — DATABASE MODELS (Mongoose)
 * ------------------------------------------------------------------------- */

/* ---- User ---- */
const userSchema = new mongoose.Schema(
  {
    username: {
      type: String,
      required: [true, 'Username is required'],
      trim: true,
      minlength: [3, 'Username must be at least 3 characters'],
      maxlength: [20, 'Username must be at most 20 characters'],
      match: [/^[A-Za-z0-9_.-]+$/, 'Username may contain letters, numbers, dot, dash and underscore only'],
    },
    /* Lower-cased mirror used for case-insensitive uniqueness + login lookups. */
    usernameLower: { type: String, required: true, unique: true, index: true, lowercase: true, trim: true },
    email: { type: String, required: [true, 'Email is required'], unique: true, index: true, lowercase: true, trim: true },
    passwordHash: { type: String, required: true, select: false },

    rating: { type: Number, default: START_RATING, min: [0, 'Rating cannot be negative'], index: true },
    peakRating: { type: Number, default: START_RATING, min: 0 },

    wins: { type: Number, default: 0, min: 0 },
    losses: { type: Number, default: 0, min: 0 },
    draws: { type: Number, default: 0, min: 0 },
    gamesPlayed: { type: Number, default: 0, min: 0 },

    isOnline: { type: Boolean, default: false, index: true },
    lastActive: { type: Date, default: Date.now, index: true },
    currentGameId: { type: mongoose.Schema.Types.ObjectId, ref: 'Game', default: null, index: true },

    preferences: {
      sound: { type: Boolean, default: true },
      showCoordinates: { type: Boolean, default: true },
      boardTheme: { type: String, enum: ['emerald', 'midnight', 'sand'], default: 'emerald' },
    },
  },
  { timestamps: true }
);

userSchema.index({ rating: -1, usernameLower: 1 });

/* Never expose private fields if a user document is ever serialised. */
userSchema.methods.toPublicJSON = function toPublicJSON() {
  return {
    id: String(this._id),
    username: this.username,
    rating: this.rating,
    peakRating: this.peakRating,
    wins: this.wins,
    losses: this.losses,
    draws: this.draws,
    gamesPlayed: this.gamesPlayed,
    isOnline: this.isOnline,
    lastActive: this.lastActive,
    createdAt: this.createdAt,
  };
};

/* ---- Game ---- */
const gameMoveSchema = new mongoose.Schema(
  {
    ply: { type: Number, required: true },
    from: { type: String, required: true, maxlength: 2 },
    to: { type: String, required: true, maxlength: 2 },
    promotion: { type: String, enum: ['q', 'r', 'b', 'n', null], default: null },
    san: { type: String, required: true },
    color: { type: String, enum: ['w', 'b'], required: true },
    piece: { type: String, enum: ['p', 'n', 'b', 'r', 'q', 'k'], required: true },
    captured: { type: String, enum: ['p', 'n', 'b', 'r', 'q', 'k', null], default: null },
    fenAfter: { type: String, required: true },
    playedAt: { type: Date, default: Date.now },
  },
  { _id: false }
);

const gameSchema = new mongoose.Schema(
  {
    gameId: { type: String, required: true, unique: true, index: true },
    mode: { type: String, enum: ['ai', 'multiplayer'], required: true, index: true },
    status: { type: String, enum: ['active', 'finished'], default: 'active', index: true },

    white: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null, index: true },
    black: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null, index: true },
    whiteName: { type: String, required: true },
    blackName: { type: String, required: true },

    /* Rating snapshots taken when the game started. */
    whiteSnapshot: { type: Number, default: 0, min: 0 },
    blackSnapshot: { type: Number, default: 0, min: 0 },

    aiColor: { type: String, enum: ['w', 'b', null], default: null },
    aiDifficulty: { type: String, enum: ['easy', 'medium', 'hard', null], default: null },

    fen: { type: String, required: true },
    moves: { type: [gameMoveSchema], default: [] },
    ply: { type: Number, default: 0, min: 0 },

    /* Pieces captured BY each side (array of piece type letters). */
    capturedByWhite: { type: [String], default: [] },
    capturedByBlack: { type: [String], default: [] },
    /* Points derived on the SERVER from the arrays above — never client supplied. */
    whiteCapturePoints: { type: Number, default: 0, min: 0 },
    blackCapturePoints: { type: Number, default: 0, min: 0 },

    result: { type: String, enum: ['white', 'black', 'draw', null], default: null },
    resultReason: {
      type: String,
      enum: [
        'checkmate',
        'resignation',
        'draw-agreed',
        'stalemate',
        'insufficient-material',
        'threefold-repetition',
        'fifty-move-rule',
        'abandoned',
        'forfeit',
        'timeout-material',
        null,
      ],
      default: null,
    },
    winner: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null },
    loser: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null },

    /* Pending draw offer: colour of the offering side, or null. */
    drawOfferBy: { type: String, enum: ['w', 'b', null], default: null },
    drawOfferAt: { type: Date, default: null },

    /* Live match clock: absolute wall-clock deadline (null for AI/practice). */
    clockEndsAt: { type: Date, default: null, index: true },
    clockSeconds: { type: Number, default: 0, min: 0 },

    /* Flat penalty applied on top of the capture transfer (forfeit/decline). */
    penaltyPoints: { type: Number, default: 0, min: 0 },
    penaltyColor: { type: String, enum: ['w', 'b', null], default: null },

    /* Audience commentary — recommendations and analysis, never board input. */
    spectatorChat: {
      type: [
        {
          _id: false,
          username: { type: String, required: true, maxlength: 20 },
          role: { type: String, enum: ['spectator', 'player'], default: 'spectator' },
          text: { type: String, required: true, maxlength: 240 },
          at: { type: Date, default: Date.now },
        },
      ],
      default: [],
    },

    /* Final rating deltas actually applied (signed, from each player's view). */
    ratingChanges: {
      white: { type: Number, default: 0 },
      black: { type: Number, default: 0 },
    },
    rated: { type: Boolean, default: false },
    finalized: { type: Boolean, default: false },

    startedAt: { type: Date, default: Date.now },
    endedAt: { type: Date, default: null },
    lastMoveAt: { type: Date, default: Date.now },
  },
  { timestamps: true }
);

gameSchema.index({ status: 1, mode: 1 });
gameSchema.index({ white: 1, status: 1 });
gameSchema.index({ black: 1, status: 1 });
gameSchema.index({ endedAt: -1 });

/* ---- Invitation ---- */
const invitationSchema = new mongoose.Schema(
  {
    from: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    to: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    fromUsername: { type: String, required: true },
    toUsername: { type: String, required: true },
    fromRating: { type: Number, required: true, min: 0 },
    status: {
      type: String,
      enum: ['pending', 'accepted', 'rejected', 'expired', 'cancelled'],
      default: 'pending',
      index: true,
    },
    gameId: { type: mongoose.Schema.Types.ObjectId, ref: 'Game', default: null },
    /* Exactly-once guard for the decline penalty (charged to the declining player). */
    penaltyApplied: { type: Boolean, default: false },
    penaltyAmount: { type: Number, default: 0, min: 0 },
    expiresAt: { type: Date, required: true, index: true },
    respondedAt: { type: Date, default: null },
  },
  { timestamps: true }
);

/* Only one PENDING invitation per (sender, recipient) pair — enforced by MongoDB. */
invitationSchema.index(
  { from: 1, to: 1 },
  { unique: true, partialFilterExpression: { status: 'pending' }, name: 'one_pending_pair' }
);
invitationSchema.index({ to: 1, status: 1, expiresAt: 1 });

/* ---- Rating history ---- */
const ratingHistorySchema = new mongoose.Schema(
  {
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    previousRating: { type: Number, required: true, min: 0 },
    change: { type: Number, required: true },
    newRating: { type: Number, required: true, min: 0 },
    reason: {
      type: String,
      enum: [
        'capture-transfer-win',
        'capture-transfer-loss',
        'draw-no-transfer',
        'invitation-rejected',
        'match-forfeit',
        'ai-game',
        'registration',
      ],
      required: true,
    },
    detail: { type: String, default: '' },
    game: { type: mongoose.Schema.Types.ObjectId, ref: 'Game', default: null, index: true },
    invitation: { type: mongoose.Schema.Types.ObjectId, ref: 'Invitation', default: null },
    opponentName: { type: String, default: '' },
    createdAt: { type: Date, default: Date.now, index: true },
  },
  { timestamps: false }
);

ratingHistorySchema.index({ user: 1, createdAt: -1 });

/* ---- Notification (persisted, so it survives refreshes) ---- */
const notificationSchema = new mongoose.Schema(
  {
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    type: {
      type: String,
      enum: ['invitation', 'invitation-rejected', 'invitation-accepted', 'game-result', 'info', 'busy', 'live-match'],
      required: true,
    },
    title: { type: String, required: true, maxlength: 160 },
    body: { type: String, required: true, maxlength: 400 },
    meta: { type: Object, default: {} },
    read: { type: Boolean, default: false, index: true },
    createdAt: { type: Date, default: Date.now, index: true },
  },
  { timestamps: false }
);

notificationSchema.index({ user: 1, createdAt: -1 });

const User = mongoose.model('User', userSchema);
const Game = mongoose.model('Game', gameSchema);
const Invitation = mongoose.model('Invitation', invitationSchema);
const RatingHistory = mongoose.model('RatingHistory', ratingHistorySchema);
const Notification = mongoose.model('Notification', notificationSchema);

/**
 * Cookie-independent session token.
 *
 * Some production setups cannot use cookies at all: plain-HTTP deployments
 * where the browser rejects `Secure` cookies, embedded/third-party frames,
 * Safari "block all cookies", or users who clear cookies between requests.
 * In those environments the cookie session is silently dropped and a player
 * who just signed up bounces straight back to the sign-in screen.
 *
 * So every sign-in also issues a bearer token (kept in localStorage by the
 * browser and sent as `x-gm-token` / `auth.token` on the socket). Only the
 * SHA-256 hash is stored, the raw token never touches the database, and the
 * record expires with the session TTL via a TTL index.
 */
const sessionTokenSchema = new mongoose.Schema(
  {
    tokenHash: { type: String, required: true, unique: true },
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    userAgent: { type: String, default: '', maxlength: 200 },
    createdAt: { type: Date, default: () => new Date(), expires: 0 },
  },
  { versionKey: false }
);
sessionTokenSchema.index({ user: 1, createdAt: -1 });
const SessionToken = mongoose.model('SessionToken', sessionTokenSchema);

/* ---------------------------------------------------------------------------
 * SECTION 4 — SHARED HELPERS (validation, chess, ratings)
 * ------------------------------------------------------------------------- */

class AppError extends Error {
  constructor(status, message, code) {
    super(message);
    this.status = status;
    this.code = code || 'error';
    this.expose = true;
  }
}
const fail = (status, message, code) => new AppError(status, message, code);

const USERNAME_RE = /^[A-Za-z0-9_.-]{3,20}$/;
const EMAIL_RE = /^[^\s@]+@[^\s@]+\.[A-Za-z]{2,}$/;

function cleanString(value, max = 200) {
  if (typeof value !== 'string') return '';
  // Strip control characters, collapse whitespace, bound the length.
  return value.replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, max);
}

function assertUsername(raw) {
  const username = cleanString(raw, 40);
  if (!USERNAME_RE.test(username)) {
    throw fail(400, 'Username must be 3-20 characters: letters, numbers, dot, dash or underscore.', 'username_invalid');
  }
  return username;
}

function assertEmail(raw) {
  const email = cleanString(raw, 254).toLowerCase();
  if (!EMAIL_RE.test(email)) throw fail(400, 'Please enter a valid email address.', 'email_invalid');
  return email;
}

function assertPassword(raw) {
  if (typeof raw !== 'string') throw fail(400, 'Password is required.', 'password_invalid');
  if (raw.length < 8) throw fail(400, 'Password must be at least 8 characters.', 'password_weak');
  if (raw.length > 128) throw fail(400, 'Password must be at most 128 characters.', 'password_invalid');
  if (!/[A-Za-z]/.test(raw) || !/[0-9]/.test(raw)) {
    throw fail(400, 'Password must contain at least one letter and one number.', 'password_weak');
  }
  return raw;
}

/** Safe ObjectId parse — returns null instead of throwing. */
function toObjectId(value) {
  if (!value) return null;
  const s = String(value);
  return /^[a-f\d]{24}$/i.test(s) ? new mongoose.Types.ObjectId(s) : null;
}

function newGameId() {
  return crypto.randomUUID();
}

/** Total capture points for a list of captured piece types. */
function capturePoints(list) {
  return (list || []).reduce((sum, t) => sum + (PIECE_VALUES[t] || 0), 0);
}

/**
 * Server-side description of a finishing position.
 * Returns null when the game continues, else { result, reason }.
 */
function terminalState(chess) {
  if (chess.isCheckmate()) {
    return { result: chess.turn() === 'w' ? 'black' : 'white', reason: 'checkmate' };
  }
  if (chess.isStalemate()) return { result: 'draw', reason: 'stalemate' };
  if (chess.isInsufficientMaterial()) return { result: 'draw', reason: 'insufficient-material' };
  if (chess.isThreefoldRepetition()) return { result: 'draw', reason: 'threefold-repetition' };
  if (chess.isDraw()) return { result: 'draw', reason: 'fifty-move-rule' };
  return null;
}

/**
 * Atomically apply a signed rating delta, clamped so ratings never go negative.
 * Returns { before, after, applied } using the pre-image returned by MongoDB.
 * The update is a single atomic pipeline update, so concurrent writers cannot
 * produce lost updates.
 */
async function applyRatingDelta(userId, requestedDelta) {
  const delta = Math.trunc(Number(requestedDelta) || 0);
  const preImage = await User.findOneAndUpdate(
    { _id: userId },
    [
      { $set: { rating: { $max: [0, { $add: ['$rating', delta] }] } } },
      { $set: { peakRating: { $max: [{ $ifNull: ['$peakRating', 0] }, '$rating'] } } },
    ],
    { returnDocument: 'before', projection: { rating: 1 }, updatePipeline: true }
  );
  if (!preImage) return null;
  const before = preImage.rating;
  const after = Math.max(0, before + delta);
  return { before, after, applied: after - before };
}

async function recordRatingHistory({ userId, before, after, reason, detail, game, invitation, opponentName }) {
  try {
    await RatingHistory.create({
      user: userId,
      previousRating: before,
      change: after - before,
      newRating: after,
      reason,
      detail: detail || '',
      game: game || null,
      invitation: invitation || null,
      opponentName: opponentName || '',
    });
  } catch (err) {
    logError('rating history', err);
  }
}

/**
 * Run `work` inside a MongoDB transaction when the deployment supports it
 * (replica set / Atlas). Standalone servers fall back to sequential execution:
 * every participant is still guarded by an atomic claim, so no double payout.
 */
async function withOptionalTransaction(work) {
  let dbSession = null;
  try {
    dbSession = await mongoose.startSession();
    let result;
    await dbSession.withTransaction(async () => {
      result = await work(dbSession);
    });
    return result;
  } catch (err) {
    const transactional =
      /Transaction numbers|replica set|not supported|Transaction API error|IllegalOperation/i.test(err.message || '');
    if (dbSession && !transactional) {
      // A genuine logical failure inside the transaction: surface it.
      await dbSession.endSession().catch(() => {});
      throw err;
    }
    if (dbSession) await dbSession.endSession().catch(() => {});
    dbSession = null;
    return work(null);
  } finally {
    if (dbSession) await dbSession.endSession().catch(() => {});
  }
}

/* ---- Per-game serialisation (prevents interleaved move application) ---- */
const gameLocks = new Map();
async function withGameLock(key, work) {
  const previous = gameLocks.get(key) || Promise.resolve();
  let release;
  const gate = new Promise((resolve) => {
    release = resolve;
  });
  const chain = previous.then(() => gate);
  gameLocks.set(key, chain);
  await previous.catch(() => {});
  try {
    return await work();
  } finally {
    release();
    /* Only the tail of the chain may drop the entry. */
    if (gameLocks.get(key) === chain) gameLocks.delete(key);
  }
}
/* Periodically release idle lock entries so the map cannot grow without bound. */
setInterval(() => {
  if (gameLocks.size > 500) gameLocks.clear();
}, 10 * 60 * 1000).unref();

/* ---------------------------------------------------------------------------
 * SECTION 5 — AI ENGINE (legal-move search, no API keys, no child process)
 * ------------------------------------------------------------------------- */

const PIECE_SQUARE = {
  p: [
    0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 10, 10, 20, 30, 30, 20, 10, 10, 5, 5, 10, 25, 25, 10, 5, 5, 0,
    0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5, 5, 10, 10, -20, -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0,
  ],
  n: [
    -50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40, -30, 0, 10, 15, 15, 10, 0, -30, -30, 5,
    15, 20, 20, 15, 5, -30, -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10, 5, -30, -40, -20, 0, 5, 5, 0,
    -20, -40, -50, -40, -30, -30, -30, -30, -40, -50,
  ],
  b: [
    -20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 10, 10, 5, 0, -10, -10, 5, 5, 10,
    10, 5, 5, -10, -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10, -10, -10, 5, 0, 0, 0, 0, 5, -10,
    -20, -10, -10, -10, -10, -10, -10, -20,
  ],
  r: [
    0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0,
    0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 5, 5, 0, 0, 0,
  ],
  q: [
    -20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 5, 5, 5, 0, -10, -5, 0, 5, 5, 5, 5,
    0, -5, 0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10, -10, 0, 5, 0, 0, 0, 0, -10, -20, -10, -10, -5, -5,
    -10, -10, -20,
  ],
  k: [
    -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40,
    -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -20, -30, -30, -40, -40, -30, -30, -20, -10, -20, -20, -20,
    -20, -20, -20, -10, 20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0, 10, 30, 20,
  ],
};

const MATERIAL = { p: 100, n: 320, b: 330, r: 500, q: 900, k: 20000 };

function squareIndex(square) {
  const file = square.charCodeAt(0) - 97;
  const rank = Number(square[1]) - 1;
  return rank * 8 + file;
}

/** Static evaluation from White's point of view (centipawns). */
function evaluateBoard(chess, ply) {
  if (chess.isCheckmate()) return chess.turn() === 'w' ? -100000 + ply : 100000 - ply;
  if (chess.isDraw() || chess.isStalemate()) return 0;
  let score = 0;
  const board = chess.board();
  for (let r = 0; r < 8; r += 1) {
    for (let f = 0; f < 8; f += 1) {
      const piece = board[r][f];
      if (!piece) continue;
      const idx = (7 - r) * 8 + f; // table row 0 = rank 8
      const table = PIECE_SQUARE[piece.type];
      const positional = table ? table[piece.color === 'w' ? idx : 63 - idx] : 0;
      const value = MATERIAL[piece.type] + positional;
      score += piece.color === 'w' ? value : -value;
    }
  }
  return score;
}

function orderMoves(moves) {
  return moves
    .slice()
    .sort(
      (a, b) =>
        (b.captured ? MATERIAL[b.captured] : 0) +
        (b.promotion ? MATERIAL[b.promotion] : 0) -
        ((a.captured ? MATERIAL[a.captured] : 0) + (a.promotion ? MATERIAL[a.promotion] : 0))
    );
}

function search(chess, depth, alpha, beta, ply) {
  if (depth <= 0 || chess.isGameOver()) return evaluateBoard(chess, ply);
  const maximizing = chess.turn() === 'w';
  let best = maximizing ? -Infinity : Infinity;
  for (const move of orderMoves(chess.moves({ verbose: true }))) {
    chess.move(move);
    const score = search(chess, depth - 1, alpha, beta, ply + 1);
    chess.undo();
    if (maximizing) {
      if (score > best) best = score;
      if (best > alpha) alpha = best;
    } else {
      if (score < best) best = score;
      if (best < beta) beta = best;
    }
    if (beta <= alpha) break;
  }
  return best;
}

/**
 * Choose a legal move for the AI. `difficulty` ∈ {easy, medium, hard}.
 * Returns a chess.js move object or null when no legal move exists.
 */
function chooseAiMove(fen, difficulty) {
  const config = AI_DIFFICULTIES[difficulty] || AI_DIFFICULTIES.medium;
  const chess = new Chess(fen);
  const moves = chess.moves({ verbose: true });
  if (!moves.length) return null;

  const scored = [];
  for (const move of orderMoves(moves)) {
    chess.move(move);
    const score = search(chess, Math.max(0, config.depth - 1), -Infinity, Infinity, 1);
    chess.undo();
    scored.push({ move, score });
  }
  scored.sort((a, b) => (chess.turn() === 'w' ? b.score - a.score : a.score - b.score));

  // Lower difficulties occasionally play a weaker (but still legal) move so the
  // engine is beatable without ever breaking the rules.
  if (config.blunder > 0 && Math.random() < config.blunder && scored.length > 1) {
    const pool = scored.slice(0, Math.min(4, scored.length));
    return pool[Math.floor(Math.random() * pool.length)].move;
  }
  return scored[0].move;
}

/* ---------------------------------------------------------------------------
 * SECTION 5B — MONGODB SRV / DNS RESOLUTION
 * ------------------------------------------------------------------------- *
 *  `mongodb+srv://` needs an SRV lookup (_mongodb._tcp.<cluster>) before a single
 *  socket is opened. Plenty of home routers and ISP resolvers refuse SRV queries,
 *  which surfaces as:
 *
 *      [error] MongoDB connection failed: querySrv ECONNREFUSED _mongodb._tcp...
 *
 *  That is a DNS failure, never a credentials failure. Resolution order:
 *      1. the operating system resolver (normal case);
 *      2. the resolvers in DNS_SERVERS (default 8.8.8.8 / 1.1.1.1 / 9.9.9.9);
 *      3. DNS-over-HTTPS (Google then Cloudflare) → we build the standard
 *         mongodb://host1:port,host2:port/... string ourselves, which needs no
 *         SRV support at all.
 *  Every step is logged, and the connection string (with its password) is never
 *  printed.
 * ------------------------------------------------------------------------- */

const SRV_PREFIX = '_mongodb._tcp.';
const DEFAULT_DNS_SERVERS = ['8.8.8.8', '1.1.1.1', '9.9.9.9'];

function isSrvUri(uri) {
  return /^mongodb\+srv:\/\//i.test(uri || '');
}

/** Split a mongodb+srv URI into its parts without losing credentials verbatim. */
function parseSrvUri(uri) {
  const match = /^mongodb\+srv:\/\/([^@/]*)@([^/?]+)(?:\/([^?]*))?(?:\?(.*))?$/i.exec(uri || '');
  if (!match) return null;
  return {
    credentials: match[1],
    host: match[2].split(',')[0].trim(),
    database: match[3] || '',
    options: match[4] || '',
  };
}

/**
 * `MONGO_SRV_HOSTS` lets you skip DNS for the cluster entirely, e.g.
 *   MONGO_SRV_HOSTS=ac-abcde-shard-00-00.xyz.mongodb.net,ac-abcde-shard-00-01...,ac-abcde-shard-00-02...
 * (Atlas → Connect → Drivers prints exactly these three hosts.)
 */
function hostsFromEnv() {
  const raw = String(process.env.MONGO_SRV_HOSTS || '').trim();
  if (!raw) return null;
  const hosts = raw
    .split(',')
    .map((entry) => entry.trim())
    .filter(Boolean)
    .map((entry) => (/^[^:]+:\d+$/.test(entry) ? entry : `${entry}:27017`));
  return hosts.length ? hosts : null;
}

/** Hosts listed in DNS_SERVERS, or the public defaults. */
function configuredDnsServers() {
  const raw = String(process.env.DNS_SERVERS || '').trim();
  const list = (raw ? raw.split(',') : DEFAULT_DNS_SERVERS)
    .map((entry) => entry.trim())
    .filter(Boolean);
  return list.length ? list : DEFAULT_DNS_SERVERS;
}

async function probeSrv(host, prefix) {
  const records = await dns.promises.resolveSrv((prefix || SRV_PREFIX) + host);
  return records.filter((record) => record && record.name);
}

/**
 * Resolve the SRV record through DNS-over-HTTPS. Returns { hosts, txtOptions }
 * (hosts already include :port) or null when the lookup cannot be completed.
 */
async function resolveSrvOverHttps(host, prefix) {
  const recordPrefix = prefix || SRV_PREFIX;
  const endpoints = [
    (name, type) => `https://dns.google/resolve?name=${encodeURIComponent(name)}&type=${type}`,
    (name, type) =>
      `https://cloudflare-dns.com/dns-query?name=${encodeURIComponent(name)}&type=${type}`,
  ];

  for (const buildUrl of endpoints) {
    try {
      const srvResponse = await fetch(buildUrl(recordPrefix + host, 'SRV'), {
        headers: { accept: 'application/dns-json' },
        signal: AbortSignal.timeout ? AbortSignal.timeout(8000) : undefined,
      });
      if (!srvResponse.ok) continue;
      const srvJson = await srvResponse.json();
      const answers = (srvJson.Answer || []).filter((answer) => Number(answer.type) === 33);
      if (!answers.length) continue;

      const hosts = answers
        .map((answer) => {
          /* SRV data: "<priority> <weight> <port> <target>" */
          const parts = String(answer.data || '').trim().split(/\s+/);
          if (parts.length < 4) return null;
          const port = parts[2];
          const target = parts[3].replace(/\.$/, '');
          return target ? `${target}:${port}` : null;
        })
        .filter(Boolean);

      let txtOptions = '';
      try {
        const txtResponse = await fetch(buildUrl(host, 'TXT'), {
          headers: { accept: 'application/dns-json' },
          signal: AbortSignal.timeout ? AbortSignal.timeout(8000) : undefined,
        });
        if (txtResponse.ok) {
          const txtJson = await txtResponse.json();
          txtOptions = (txtJson.Answer || [])
            .filter((answer) => Number(answer.type) === 16)
            .map((answer) => String(answer.data || '').replace(/^"|"$/g, ''))
            .join('&');
        }
      } catch (err) {
        /* TXT only carries replicaSet/authSource defaults — not essential. */
      }

      if (hosts.length) return { hosts, txtOptions };
    } catch (err) {
      /* try the next DoH provider */
    }
  }
  return null;
}

/** Build a standard connection string from the SRV results. */
function buildDirectUri(parsed, resolved) {
  const params = new URLSearchParams(
    [parsed.options, resolved.txtOptions].filter(Boolean).join('&')
  );
  if (!params.has('ssl') && !params.has('tls')) params.set('tls', 'true');
  if (!params.has('authSource')) params.set('authSource', 'admin');
  if (!params.has('retryWrites')) params.set('retryWrites', 'true');
  const credentials = parsed.credentials ? `${parsed.credentials}@` : '';
  return `mongodb://${credentials}${resolved.hosts.join(',')}/${parsed.database}?${params.toString()}`;
}

/**
 * Turn MONGO_URI into a connection string this machine can actually use.
 * Non-SRV URIs pass straight through untouched.
 */
async function resolveMongoUri(rawUri) {
  if (!isSrvUri(rawUri)) return { uri: rawUri, srv: false, changed: false };

  const parsed = parseSrvUri(rawUri);
  if (!parsed) return { uri: rawUri, srv: true, changed: false };

  /* 1. operating system resolver */
  try {
    await probeSrv(parsed.host);
    return { uri: rawUri, srv: true, changed: false };
  } catch (err) {
    log(
      `DNS: SRV lookup for ${SRV_PREFIX}${parsed.host} failed with the system resolver ` +
        `(${err.code || err.message}). Trying alternate DNS servers…`
    );
  }

  /* 2. explicit / public resolvers */
  const fallbackServers = configuredDnsServers();
  const previousServers = dns.getServers();
  let publicDnsWorked = false;
  try {
    dns.setServers(fallbackServers);
    await probeSrv(parsed.host);
    publicDnsWorked = true;
    log(`DNS: SRV lookup succeeded via ${fallbackServers.join(', ')} — keeping these resolvers for this process.`);
    return { uri: rawUri, srv: true, changed: false, dnsServers: fallbackServers };
  } catch (err) {
    log(`DNS: SRV lookup also failed via ${fallbackServers.join(', ')} (${err.code || err.message}).`);
  } finally {
    if (!publicDnsWorked) {
      /* Leave the machine's own resolver config in place for other lookups. */
      try {
        dns.setServers(previousServers);
      } catch (err) {
        /* ignore */
      }
    }
  }

  /* 3. an explicit host list from .env — no DNS involved at all */
  const envHosts = hostsFromEnv();
  if (envHosts) {
    const txtOptions = String(process.env.MONGO_REPLICA_SET || '').trim()
      ? `replicaSet=${String(process.env.MONGO_REPLICA_SET).trim()}`
      : '';
    const uri = buildDirectUri(parsed, { hosts: envHosts, txtOptions });
    log(`DNS: using MONGO_SRV_HOSTS from .env (${envHosts.join(', ')}) — no SRV lookup needed.`);
    return { uri, srv: false, changed: true, hosts: envHosts };
  }

  /* 4. DNS over HTTPS → hash out a plain mongodb:// string */
  log('DNS: falling back to DNS-over-HTTPS to resolve the Atlas cluster…');
  const resolved = await resolveSrvOverHttps(parsed.host);
  if (resolved) {
    const uri = buildDirectUri(parsed, resolved);
    log(
      `DNS: resolved ${parsed.host} over HTTPS to ${resolved.hosts.join(', ')} — ` +
        'using a standard mongodb:// connection string (no SRV lookup needed).'
    );
    return { uri, srv: false, changed: true, hosts: resolved.hosts };
  }

  return { uri: rawUri, srv: true, changed: false, unresolved: true };
}

/** Human-readable advice for a failed connection attempt. */
function mongoFailureAdvice(err) {
  const message = String((err && (err.message || err.code)) || '');
  const lines = [];

  if (/querySrv|_mongodb\._tcp|resolveSrv/i.test(message)) {
    lines.push(
      'This is a DNS problem: mongodb+srv:// needs an SRV record lookup and your',
      'resolver refused it (querySrv ECONNREFUSED / ENOTFOUND / ESERVFAIL).',
      'Fix any of the following, then run `node server` again:',
      '  a) Add    DNS_SERVERS=8.8.8.8,1.1.1.1    to .env (uses Google/Cloudflare DNS).',
      '  b) Windows: Settings → Network → Adapter options → IPv4 → set DNS to',
      '     8.8.8.8 and 1.1.1.1, then `ipconfig /flushdns` and restart the terminal.',
      '  c) MongoDB Atlas → Connect → Drivers → Node.js: copy the string that starts',
      '     with mongodb:// (three cluster hosts). Paste it as MONGO_URI — it needs',
      '     no SRV lookup at all. URL-encode special characters in the password.',
      '  d) Set MONGO_SRV_HOSTS in .env to the three hosts Atlas shows (Connect → Drivers);',
      '     that bypasses DNS for the cluster completely.',
      '  e) If a VPN/corporate network blocks DNS, disable it for this connection.'
    );
  } else if (/authentication failed|bad auth|SCRAM|auth/i.test(message)) {
    lines.push(
      'The cluster was reached but rejected the credentials.',
      '  • Check the database user name and password in MONGO_URI.',
      '  • URL-encode special characters in the password (@ → %40, : → %3A, # → %23, / → %2F).',
      '  • Confirm the user exists in Atlas → Database Access.'
    );
  } else if (/ENOTFOUND|EAI_AGAIN|ETIMEDOUT|Server selection timed out|ECONNREFUSED/i.test(message)) {
    lines.push(
      'The host name was not reachable at the network level.',
      '  • Atlas → Network Access: add your current public IP (or 0.0.0.0/0 while testing).',
      '  • Confirm the cluster is running (not paused) and the host name is exact.',
      '  • A firewall, VPN or proxy may be blocking outbound port 27017.'
    );
  } else if (/SSL|TLS|certificate|self.signed|ssl/i.test(message)) {
    lines.push(
      'TLS negotiation failed.',
      '  • MongoDB Atlas requires TLS: keep tls=true in the connection string.',
      '  • A local/self-hosted server usually has no TLS: set MONGO_TLS=false in .env.',
      '  • A corporate TLS-inspecting proxy may need to be disabled.'
    );
  } else {
    lines.push('Check MONGO_URI, the Atlas IP allow-list, and that the cluster is running.');
  }
  return lines;
}

/* ---------------------------------------------------------------------------
 * SECTION 6 — EXPRESS APPLICATION, SESSION, SECURITY
 * ------------------------------------------------------------------------- */

const app = express();
const server = http.createServer(app);
/** @type {import('socket.io').Server|null} */
let io = null;

/* Needed behind Render/Heroku/Nginx/Vercel so req.secure and req.ip are right,
 * which in turn decides whether the session cookie may carry the Secure flag.
 * TRUST_PROXY accepts true | false | <number of hops> | loopback | linklocal |
 * uniquelocal. Default: one hop in production (the usual single reverse proxy),
 * none in development. */
const TRUST_PROXY_RAW = String(process.env.TRUST_PROXY || '').trim().toLowerCase();
const TRUST_PROXY_VALUE = (() => {
  if (!TRUST_PROXY_RAW) return IS_PROD ? 1 : false;
  if (TRUST_PROXY_RAW === 'false' || TRUST_PROXY_RAW === '0' || TRUST_PROXY_RAW === 'no') return false;
  if (TRUST_PROXY_RAW === 'true' || TRUST_PROXY_RAW === 'yes') return 1;
  if (/^\d+$/.test(TRUST_PROXY_RAW)) return Number(TRUST_PROXY_RAW);
  return TRUST_PROXY_RAW; // 'loopback', 'linklocal', 'uniquelocal' or a csv of subnets
})();
if (TRUST_PROXY_VALUE !== false) app.set('trust proxy', TRUST_PROXY_VALUE);

app.disable('x-powered-by');

/* Security headers. `frameguard` is disabled so the app can be embedded in the
 * platform preview iframe; enable it (X-Frame-Options: SAMEORIGIN) in production
 * if you do not need embedding. */
app.use(
  helmet({
    contentSecurityPolicy: {
      useDefaults: true,
      directives: {
        defaultSrc: ["'self'"],
        scriptSrc: ["'self'", "'unsafe-inline'"],
        styleSrc: ["'self'", "'unsafe-inline'", 'https://fonts.googleapis.com'],
        imgSrc: ["'self'", 'data:', 'blob:'],
        fontSrc: ["'self'", 'data:', 'https://fonts.gstatic.com'],
        connectSrc: ["'self'", 'ws:', 'wss:'],
        objectSrc: ["'none'"],
        baseUri: ["'self'"],
        formAction: ["'self'"],
      },
    },
    crossOriginEmbedderPolicy: false,
    frameguard: false,
    referrerPolicy: { policy: 'same-origin' },
  })
);
app.use((req, res, next) => {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('Permissions-Policy', 'geolocation=(), microphone=(), camera=()');
  next();
});

app.use(express.json({ limit: '32kb' }));
app.use(express.urlencoded({ extended: false, limit: '32kb' }));

/**
 * Sessions live in MongoDB (connect-mongo). The concrete store is attached in
 * start() once the connection string has been resolved (SRV/DNS handling), so
 * express-session can be constructed at module load. Requests that arrive
 * before the store is attached are queued for a fraction of a second — in
 * practice none, because listening only starts after the store is ready.
 * If the database is unreachable the app exits with a clear message instead of
 * silently serving an in-memory session store.
 */
class DeferredSessionStore extends session.Store {
  constructor() {
    super();
    this.inner = null;
    this.queue = [];
  }

  attach(store) {
    this.inner = store;
    const queued = this.queue;
    this.queue = [];
    for (const run of queued) {
      try {
        run(store);
      } catch (err) {
        logError('session store attach', err);
      }
    }
  }

  _defer(method, args) {
    if (this.inner) {
      this.inner[method](...args);
      return;
    }
    this.queue.push((store) => store[method](...args));
  }

  get(sid, callback) {
    this._defer('get', [sid, callback]);
  }

  set(sid, sessionData, callback) {
    this._defer('set', [sid, sessionData, callback]);
  }

  destroy(sid, callback) {
    this._defer('destroy', [sid, callback]);
  }

  touch(sid, sessionData, callback) {
    this._defer('touch', [sid, sessionData, callback]);
  }

  length(callback) {
    if (this.inner) return this.inner.length(callback);
    return callback(null, 0);
  }

  clear(callback) {
    if (this.inner) return this.inner.clear(callback);
    return callback(null);
  }

  all(callback) {
    if (this.inner) return this.inner.all(callback);
    return callback(null, []);
  }

  close() {
    if (this.inner && typeof this.inner.close === 'function') return this.inner.close();
    return undefined;
  }
}

const sessionStore = new DeferredSessionStore();

/** Create the persistent store for an already-resolved connection string. */
function createMongoSessionStore(connectionUri) {
  return MongoStore.create({
    mongoUrl: connectionUri,
    dbName: DB_NAME,
    collectionName: 'sessions',
    ttl: Math.floor(SESSION_TTL_MS / 1000),
    autoRemove: 'native',
    crypto: { secret: SESSION_SECRET || 'dev-fallback-secret' },
  });
}

/**
 * Cookie security. A `Secure` cookie is silently discarded by the browser when
 * the page is served over plain HTTP, which used to leave freshly registered
 * players stuck on the sign-in screen in production. `'auto'` lets
 * express-session decide per request (Secure only when the request is HTTPS),
 * and COOKIE_SECURE=true|false pins it explicitly.
 */
const COOKIE_SECURE = (() => {
  const raw = String(process.env.COOKIE_SECURE || '').trim().toLowerCase();
  if (raw === 'true' || raw === 'always') return true;
  if (raw === 'false' || raw === 'never') return false;
  return 'auto';
})();

/* SameSite policy. 'lax' (default) survives normal navigation, OAuth-style
 * returns and iframe-free hosting. 'none' is only meaningful together with
 * Secure, so it forces Secure on. */
const COOKIE_SAME_SITE = (() => {
  const raw = String(process.env.COOKIE_SAMESITE || '').trim().toLowerCase();
  if (raw === 'strict') return 'strict';
  if (raw === 'none') return 'none';
  return 'lax';
})();

/* Optional cookie domain for sub-domain deployments (e.g. .example.com).
 * Left empty the cookie is host-only, which is what most hosts need. */
const COOKIE_DOMAIN = String(process.env.COOKIE_DOMAIN || '').trim() || undefined;

const sessionMiddleware = session({
  name: 'grandmaster.sid',
  secret: SESSION_SECRET || crypto.randomBytes(32).toString('hex'),
  resave: false,
  saveUninitialized: false,
  rolling: true,
  store: sessionStore,
  cookie: {
    httpOnly: true,
    sameSite: COOKIE_SAME_SITE,
    /* 'none' without Secure is rejected by every modern browser. */
    secure: COOKIE_SAME_SITE === 'none' ? true : COOKIE_SECURE,
    ...(COOKIE_DOMAIN ? { domain: COOKIE_DOMAIN } : {}),
    maxAge: SESSION_TTL_MS,
    path: '/',
  },
});
/** Wrap async route handlers so rejections reach the error middleware. */
const wrap = (fn) => (req, res, next) => Promise.resolve(fn(req, res, next)).catch(next);

app.use(sessionMiddleware);

/**
 * Cookie fallback. If the browser dropped the session cookie (Secure cookie on
 * plain HTTP, blocked third-party cookies, cleared storage), the request still
 * carries a bearer token. We rebuild the session from it so the app behaves
 * identically with or without cookies.
 */
app.use(
  wrap(async (req, res, next) => {
    const header = req.get('x-gm-token');
    const bearer = /^Bearer\s+(.+)$/i.exec(req.get('authorization') || '');
    const raw = cleanString(header || (bearer ? bearer[1] : ''), 200);
    if (!raw) return next();

    /* Always make sure the browser also gets a cookie again, so the next request
     * works even if it stops sending the header (e.g. after a form post). */
    if (req.session && req.session.userId) return next();

    const userId = await resolveSessionToken(raw);
    if (!userId) return next();
    const user = await User.findById(userId).select('username').lean();
    if (!user) return next();
    if (!req.session) return next();
    req.session.userId = userId;
    req.session.tokenAuth = true;
    req.session.tokenHash = hashSessionToken(raw);
    req.session.createdAt = req.session.createdAt || Date.now();
    return next();
  })
);

/* ---- Rate limiters ----
 * DISABLE_RATE_LIMITS=true is honoured only outside production so an automated
 * test suite can drive many accounts from one IP. Never set it in production. */
const RATE_LIMITS_OFF = !IS_PROD && String(process.env.DISABLE_RATE_LIMITS || 'false').toLowerCase() === 'true';
const passthroughLimiter = (req, res, next) => next();
const limiter = (options) => (RATE_LIMITS_OFF ? passthroughLimiter : rateLimit(options));
const authLimiter = limiter({
  windowMs: 15 * 60 * 1000,
  limit: 40,
  standardHeaders: 'draft-7',
  legacyHeaders: false,
  message: { error: 'Too many authentication attempts. Please wait a few minutes and try again.' },
});
const apiLimiter = limiter({
  windowMs: 60 * 1000,
  limit: 240,
  standardHeaders: 'draft-7',
  legacyHeaders: false,
  message: { error: 'Too many requests. Please slow down.' },
});
const inviteLimiter = limiter({
  windowMs: 5 * 60 * 1000,
  limit: 40,
  standardHeaders: 'draft-7',
  legacyHeaders: false,
  message: { error: 'Too many invitations. Please wait a moment.' },
});
const coachLimiter = limiter({
  windowMs: 60 * 1000,
  limit: 12,
  standardHeaders: 'draft-7',
  legacyHeaders: false,
  message: { error: 'Coach is busy. Please wait a moment.' },
});

/* ---- Auth guards ---- */
function requireAuth(req, res, next) {
  if (!req.session || !req.session.userId) return res.status(401).json({ error: 'Please sign in to continue.', code: 'unauthenticated' });
  next();
}
function requireGuest(req, res, next) {
  /* A cookie-less fallback session must not lock the user out of the forms —
   * they are precisely the people who may need to sign in again. */
  if (req.session && req.session.userId && !req.session.tokenAuth) {
    return res.status(400).json({ error: 'You are already signed in.', code: 'already_authenticated' });
  }
  next();
}


/** SHA-256 of a bearer token — the only form ever written to MongoDB. */
function hashSessionToken(raw) {
  return crypto.createHash('sha256').update(String(raw)).digest('hex');
}

/**
 * Issue a new bearer token for a user. Returns the raw token exactly once.
 * Old tokens for the same user are pruned so a stolen-but-unused token cannot
 * pile up (keep the 12 most recent devices/sessions).
 */
async function issueSessionToken(userId, req) {
  const raw = crypto.randomBytes(32).toString('base64url');
  const ua = cleanString(req?.get?.('user-agent') || '', 200);
  try {
    await SessionToken.create({ tokenHash: hashSessionToken(raw), user: userId, userAgent: ua });
    const stale = await SessionToken.find({ user: userId })
      .sort({ createdAt: -1 })
      .skip(12)
      .select('_id')
      .lean();
    if (stale.length) await SessionToken.deleteMany({ _id: { $in: stale.map((row) => row._id) } });
  } catch (err) {
    /* A token is a convenience fallback: never block a successful sign-in. */
    logError('issueSessionToken', err);
    return null;
  }
  return raw;
}

/** Resolve a raw bearer token to a live user id, or null. */
async function resolveSessionToken(raw, cache) {
  if (typeof raw !== 'string' || raw.length < 20 || raw.length > 200) return null;
  const tokenHash = hashSessionToken(raw);
  const box = cache || tokenCache;
  const hit = box.get(tokenHash);
  if (hit && hit.expiresAt > Date.now()) return hit.userId;
  let row = null;
  try {
    row = await SessionToken.findOne({ tokenHash }).select('user createdAt').lean();
  } catch (err) {
    if (!(err && err.code === 11000)) logError('resolveSessionToken', err);
    return null;
  }
  if (!row) return null;
  const age = Date.now() - new Date(row.createdAt).getTime();
  if (age > SESSION_TTL_MS) {
    SessionToken.deleteOne({ _id: row._id }).catch(() => {});
    return null;
  }
  const entry = { userId: String(row.user), expiresAt: Date.now() + 30_000 };
  box.set(tokenHash, entry);
  if (box.size > 5000) box.clear();
  return entry.userId;
}

/** Small in-process cache so the fallback costs one query per 30 s per token. */
const tokenCache = new Map();

/** Forget every token belonging to a user (sign-out). */
async function revokeSessionTokens(userId, keepRaw) {
  try {
    const query = { user: userId };
    if (keepRaw) query.tokenHash = { $ne: hashSessionToken(keepRaw) };
    await SessionToken.deleteMany(query);
  } catch (err) {
    logError('revokeSessionTokens', err);
  }
  tokenCache.clear();
}

/** Regenerate the session id (prevents session fixation) and store the user id. */
function establishSession(req, userId) {
  return new Promise((resolve, reject) => {
    req.session.regenerate((err) => {
      if (err) return reject(err);
      req.session.userId = String(userId);
      req.session.createdAt = Date.now();
      req.session.save((saveErr) => (saveErr ? reject(saveErr) : resolve()));
    });
  });
}

/* ---------------------------------------------------------------------------
 * SECTION 7 — PRESENCE, NOTIFICATIONS, SOCKET ROOMS
 * ------------------------------------------------------------------------- */

/** userId(string) -> Set<socketId> so multiple tabs do not mark users offline. */
const presence = new Map();

function socketsForUser(userId) {
  return Array.from(presence.get(String(userId)) || []);
}

function userRoom(userId) {
  return `user:${String(userId)}`;
}
function gameRoomByGameId(gameId) {
  return `game:${String(gameId)}`;
}

/** Deliver a socket event to every tab of a user. */
function emitToUser(userId, event, payload) {
  if (!io) return;
  io.to(userRoom(userId)).emit(event, payload);
}

/** Persist a notification and push it in real time. */
async function notifyUser(userId, { type, title, body, meta = {} }) {
  try {
    const doc = await Notification.create({ user: userId, type, title, body, meta });
    emitToUser(userId, 'notification', {
      id: String(doc._id),
      type: doc.type,
      title: doc.title,
      body: doc.body,
      meta: doc.meta,
      createdAt: doc.createdAt,
    });
    return doc;
  } catch (err) {
    logError('notifyUser', err);
    return null;
  }
}

async function setOnline(userId, online) {
  const now = new Date();
  if (online) {
    await User.updateOne({ _id: userId }, { $set: { isOnline: true, lastActive: now } });
  } else {
    await User.updateOne({ _id: userId }, { $set: { isOnline: false, lastActive: now } });
  }
  if (io) {
    const user = await User.findById(userId).select('username rating isOnline').lean();
    if (user) {
      io.emit('presence:update', {
        userId: String(user._id),
        username: user.username,
        rating: user.rating,
        online: user.isOnline,
      });
    }
  }
}

/* ---------------------------------------------------------------------------
 * SECTION 8 — GAME SERVICE (creation, moves, termination, ratings)
 * ------------------------------------------------------------------------- */

function userNameFor(game, color) {
  return color === 'w' ? game.whiteName : game.blackName;
}

function userIdFor(game, color) {
  return color === 'w' ? game.white : game.black;
}

function colorOfPlayer(game, userId) {
  const id = String(userId);
  if (game.white && String(game.white) === id) return 'w';
  if (game.black && String(game.black) === id) return 'b';
  return null;
}

/** chess.js compatibility helpers (v1 API, with defensive fallbacks). */
function chessInCheck(chess) {
  if (typeof chess.inCheck === 'function') return chess.inCheck();
  if (typeof chess.isCheck === 'function') return chess.isCheck();
  return false;
}

/** Squares the side to move may legally move to, grouped by origin square. */
function legalMoveMap(chess) {
  const map = {};
  let moves = [];
  try {
    moves = chess.moves({ verbose: true });
  } catch (err) {
    moves = [];
  }
  for (const move of moves) {
    if (!map[move.from]) map[move.from] = [];
    map[move.from].push({
      to: move.to,
      promotion: Boolean(move.promotion),
      capture: typeof move.flags === 'string' && (move.flags.indexOf('c') !== -1 || move.flags.indexOf('e') !== -1),
      san: move.san,
    });
  }
  return map;
}

function kingSquareOf(chess, color) {
  for (const row of chess.board()) {
    for (const square of row) {
      if (square && square.type === 'k' && square.color === color) return square.square;
    }
  }
  return null;
}

/** Public, viewer-scoped serialisation of a game. */
function serializeGame(game, viewerId) {
  const viewerColor = colorOfPlayer(game, viewerId);
  const moves = (game.moves || []).map((m) => ({
    ply: m.ply,
    san: m.san,
    from: m.from,
    to: m.to,
    color: m.color,
    piece: m.piece,
    captured: m.captured,
  }));
  const last = moves[moves.length - 1] || null;
  /* The board is authoritative here: the browser receives the position AND the
   * list of legal moves, so it can never display or submit an illegal move. */
  const chess = new Chess(game.fen);
  const turn = chess.turn();
  const inCheck = chessInCheck(chess);
  const over = game.status === 'finished';
  return {
    gameId: game.gameId,
    id: String(game._id),
    mode: game.mode,
    status: game.status,
    fen: game.fen,
    ply: game.ply,
    turn,
    legal: over ? {} : legalMoveMap(chess),
    inCheck,
    kingSquare: inCheck ? kingSquareOf(chess, turn) : null,
    checkmate: !over && typeof chess.isCheckmate === 'function' ? chess.isCheckmate() : false,
    moves,
    lastMove: last ? { from: last.from, to: last.to } : null,
    captured: {
      w: game.capturedByWhite || [],
      b: game.capturedByBlack || [],
    },
    capturePoints: {
      w: game.whiteCapturePoints || 0,
      b: game.blackCapturePoints || 0,
    },
    players: {
      w: {
        id: game.white ? String(game.white) : null,
        username: game.whiteName,
        rating: game.whiteSnapshot,
        isAi: !game.white,
      },
      b: {
        id: game.black ? String(game.black) : null,
        username: game.blackName,
        rating: game.blackSnapshot,
        isAi: !game.black,
      },
    },
    you: viewerColor,
    /* 'player' for the two participants, 'spectator' for the audience. */
    role: viewerColor ? 'player' : 'spectator',
    drawOfferBy: game.drawOfferBy || null,
    result: game.result || null,
    resultReason: game.resultReason || null,
    ratingChanges: { w: game.ratingChanges?.white || 0, b: game.ratingChanges?.black || 0 },
    penalty: { points: game.penaltyPoints || 0, color: game.penaltyColor || null },
    rated: !!game.rated,
    aiDifficulty: game.aiDifficulty || null,
    clockEndsAt: game.clockEndsAt || null,
    clockSeconds: game.clockSeconds || 0,
    /* the browser derives the countdown from this, immune to client clock drift */
    serverTime: Date.now(),
    spectators: spectatorCount(game.gameId),
    chat: (game.spectatorChat || []).slice(-60).map((entry) => ({
      username: entry.username,
      role: entry.role,
      text: entry.text,
      at: entry.at,
    })),
    startedAt: game.startedAt,
    endedAt: game.endedAt,
  };
}

/** Number of sockets currently watching a match. */
function spectatorCount(gameId) {
  if (!io) return 0;
  const room = io.sockets.adapter.rooms.get(spectatorRoom(gameId));
  return room ? room.size : 0;
}

function spectatorRoom(gameId) {
  return `spectate:${String(gameId)}`;
}

/**
 * Decide a timed-out match on captured material.
 * Returns the terminal descriptor consumed by finalizeGame().
 */
function materialVerdict(game) {
  const white = game.whiteCapturePoints || 0;
  const black = game.blackCapturePoints || 0;
  if (white > black) return { result: 'white', reason: 'timeout-material', white, black };
  if (black > white) return { result: 'black', reason: 'timeout-material', white, black };
  return { result: 'draw', reason: 'timeout-material', white, black };
}

/** Claim the single "active game" seat on a user document. */
async function claimSeat(userId, gameObjectId) {
  const res = await User.updateOne(
    { _id: userId, currentGameId: null },
    { $set: { currentGameId: gameObjectId } }
  );
  return res.modifiedCount === 1;
}

async function releaseSeats(gameObjectId) {
  await User.updateMany({ currentGameId: gameObjectId }, { $set: { currentGameId: null } });
}

/** Create a multiplayer game for two authenticated users. */
async function startMultiplayerGame(userAId, userBId) {
  if (String(userAId) === String(userBId)) throw fail(400, 'You cannot play against yourself.', 'self_play');
  const [a, b] = await Promise.all([User.findById(userAId), User.findById(userBId)]);
  if (!a || !b) throw fail(404, 'One of the players no longer exists.', 'player_missing');

  const chess = new Chess();
  const aIsWhite = crypto.randomInt(2) === 0;
  const white = aIsWhite ? a : b;
  const black = aIsWhite ? b : a;

  const now = new Date();
  const game = await Game.create({
    gameId: newGameId(),
    mode: 'multiplayer',
    status: 'active',
    white: white._id,
    black: black._id,
    whiteName: white.username,
    blackName: black.username,
    whiteSnapshot: white.rating,
    blackSnapshot: black.rating,
    fen: chess.fen(),
    startedAt: now,
    lastMoveAt: now,
    /* Live PvP matches run against a single 10-minute match clock. */
    clockSeconds: PVP_MATCH_SECONDS,
    clockEndsAt: new Date(now.getTime() + PVP_MATCH_SECONDS * 1000),
  });

  const [seatA, seatB] = await Promise.all([claimSeat(a._id, game._id), claimSeat(b._id, game._id)]);
  if (!seatA || !seatB) {
    await releaseSeats(game._id);
    await Game.deleteOne({ _id: game._id });
    throw fail(409, 'One of the players just started another match. Please try again.', 'busy');
  }
  return game;
}

/** Create an AI game for one user. */
async function startAiGame(userId, difficulty, colorChoice) {
  const diff = AI_DIFFICULTIES[difficulty] ? difficulty : 'medium';
  const user = await User.findById(userId);
  if (!user) throw fail(404, 'Account not found.', 'player_missing');
  if (user.currentGameId) throw fail(409, 'You are already in an active match. Finish or resign it first.', 'busy');

  const color = colorChoice === 'w' || colorChoice === 'b' ? colorChoice : crypto.randomInt(2) === 0 ? 'w' : 'b';
  const aiColor = color === 'w' ? 'b' : 'w';
  const chess = new Chess();
  const aiName = `Grandmaster AI · ${AI_DIFFICULTIES[diff].label}`;

  const game = await Game.create({
    gameId: newGameId(),
    mode: 'ai',
    status: 'active',
    white: color === 'w' ? user._id : null,
    black: color === 'b' ? user._id : null,
    whiteName: color === 'w' ? user.username : aiName,
    blackName: color === 'b' ? user.username : aiName,
    whiteSnapshot: color === 'w' ? user.rating : 0,
    blackSnapshot: color === 'b' ? user.rating : 0,
    aiColor,
    aiDifficulty: diff,
    fen: chess.fen(),
    startedAt: new Date(),
    lastMoveAt: new Date(),
  });

  const claimed = await claimSeat(user._id, game._id);
  if (!claimed) {
    await Game.deleteOne({ _id: game._id });
    throw fail(409, 'You are already in an active match. Finish or resign it first.', 'busy');
  }
  return game;
}

function broadcastGame(game, extra = {}) {
  if (!io) return;
  for (const color of ['w', 'b']) {
    const uid = userIdFor(game, color);
    if (!uid) continue;
    io.to(userRoom(uid)).emit('game:state', { ...serializeGame(game, uid), ...extra });
  }
  /* The audience sees the same authoritative position, read-only. */
  io.to(spectatorRoom(game.gameId)).emit('game:state', { ...spectateState(game), ...extra });
}

/** Read-only state payload for spectators (no player identity shortcuts). */
function spectateState(game) {
  return { ...serializeGame(game, null), spectating: true };
}

/** Push the current spectator count to players and the audience. */
function broadcastSpectatorCount(gameId) {
  if (!io) return;
  const count = spectatorCount(gameId);
  io.to(spectatorRoom(gameId)).emit('spectate:count', { gameId: String(gameId), count });
  Game.findOne({ gameId: String(gameId) })
    .select('white black gameId')
    .lean()
    .then((game) => {
      if (!game) return;
      for (const color of ['w', 'b']) {
        const uid = userIdFor(game, color);
        if (uid) emitToUser(uid, 'spectate:count', { gameId: String(gameId), count });
      }
    })
    .catch(() => {});
}

/** Announce / unannounce a live match to every connected user. */
function broadcastLiveMatch(event, game) {
  if (!io || !game) return;
  io.emit(event, {
    gameId: game.gameId,
    white: game.whiteName,
    black: game.blackName,
    whiteRating: game.whiteSnapshot,
    blackRating: game.blackSnapshot,
    spectators: spectatorCount(game.gameId),
    clockEndsAt: game.clockEndsAt || null,
    clockSeconds: game.clockSeconds || 0,
    startedAt: game.startedAt,
  });
}

/**
 * Finalise a finished game exactly once and apply the capture-based rating
 * transfer. The atomic claim on `status: 'active'` guarantees a single payout
 * even if two players (or duplicate events) race.
 */
async function finalizeGame(gameDoc, terminal, options = {}) {
  const winnerColor = terminal.result === 'draw' ? null : terminal.result;
  const loserColor = winnerColor === 'white' ? 'black' : winnerColor === 'black' ? 'white' : null;
  const wc = winnerColor === 'white' ? 'w' : winnerColor === 'black' ? 'b' : null;
  const lc = wc === 'w' ? 'b' : wc === 'b' ? 'w' : null;

  const claim = await Game.findOneAndUpdate(
    { _id: gameDoc._id, status: 'active' },
    {
      $set: {
        status: 'finished',
        result: terminal.result,
        resultReason: terminal.reason,
        winner: wc ? userIdFor(gameDoc, wc) : null,
        loser: lc ? userIdFor(gameDoc, lc) : null,
        endedAt: new Date(),
        drawOfferBy: null,
        drawOfferAt: null,
        finalized: false,
      },
    },
    { returnDocument: 'after' }
  );

  if (!claim) {
    /* Someone else already finalised this game — return the stored result. */
    return Game.findById(gameDoc._id);
  }

  const rated = claim.mode === 'multiplayer' || AI_GAMES_AFFECT_RATING;
  const changes = { white: 0, black: 0 };
  /* Flat penalty (leaver forfeits / decliner pays) applied after the transfer. */
  const penaltyColorLetter = options.penaltyColor === 'w' || options.penaltyColor === 'b' ? options.penaltyColor : null;
  const penaltyRequested = Math.max(0, Math.trunc(Number(options.penaltyPoints) || 0));

  try {
    if (rated && wc && lc) {
      const winnerId = userIdFor(claim, wc);
      const loserId = userIdFor(claim, lc);
      const points = wc === 'w' ? claim.whiteCapturePoints || 0 : claim.blackCapturePoints || 0;

      if (winnerId && loserId && points > 0) {
        const loserDoc = await User.findById(loserId).select('rating username').lean();
        /* Never take more than the loser actually has: ratings cannot go negative. */
        const transfer = Math.min(points, loserDoc ? loserDoc.rating : 0);
        if (transfer > 0) {
          /* Both halves of the transfer run inside one transaction on replica
           * sets (Atlas), and fall back to sequential writes on standalone
           * servers — the atomic claim above already prevents double payouts. */
          const applied = await withOptionalTransaction(async () => {
            const wRes = await applyRatingDelta(winnerId, transfer);
            const lRes = await applyRatingDelta(loserId, -transfer);
            return { wRes, lRes };
          });
          const { wRes, lRes } = applied;
          /* `changes` is keyed by the schema's colour names, not board letters. */
          changes[wc === 'w' ? 'white' : 'black'] = wRes ? wRes.applied : 0;
          changes[lc === 'w' ? 'white' : 'black'] = lRes ? lRes.applied : 0;
          await recordRatingHistory({
            userId: winnerId,
            before: wRes.before,
            after: wRes.after,
            reason: 'capture-transfer-win',
            detail: `${points} capture point(s) earned; ${changes[wc === 'w' ? 'white' : 'black']} point(s) transferred from ${loserDoc ? loserDoc.username : 'opponent'}.`,
            game: claim._id,
            opponentName: loserDoc ? loserDoc.username : '',
          });
          await recordRatingHistory({
            userId: loserId,
            before: lRes.before,
            after: lRes.after,
            reason: 'capture-transfer-loss',
            detail: `Opponent captured ${points} point(s) of material; ${Math.abs(changes[lc === 'w' ? 'white' : 'black'])} point(s) transferred.`,
            game: claim._id,
            opponentName: winnerDocName(claim, wc),
          });
        }
      }
      /* Stats: only meaningful for games between two accounts. */
      const winnerIdFinal = userIdFor(claim, wc);
      const loserIdFinal = userIdFor(claim, lc);
      if (winnerIdFinal) {
        await User.updateOne({ _id: winnerIdFinal }, { $inc: { wins: 1, gamesPlayed: 1 } });
      }
      if (loserIdFinal) {
        await User.updateOne({ _id: loserIdFinal }, { $inc: { losses: 1, gamesPlayed: 1 } });
      }
    } else if (rated && terminal.result === 'draw' && terminal.reason !== 'abandoned') {
      for (const color of ['w', 'b']) {
        const uid = userIdFor(claim, color);
        if (!uid) continue;
        const snapshot = await User.findById(uid).select('rating').lean();
        if (!snapshot) continue;
        await recordRatingHistory({
          userId: uid,
          before: snapshot.rating,
          after: snapshot.rating,
          reason: 'draw-no-transfer',
          detail: 'Draw: no capture-based points are transferred.',
          game: claim._id,
          opponentName: userNameFor(claim, color === 'w' ? 'b' : 'w'),
        });
        await User.updateOne({ _id: uid }, { $inc: { draws: 1, gamesPlayed: 1 } });
      }
    }

    /* ---- flat penalty (never creates a negative rating) ---- */
    if (penaltyColorLetter && penaltyRequested > 0) {
      const penalizedId = userIdFor(claim, penaltyColorLetter);
      if (penalizedId) {
        const before = await User.findById(penalizedId).select('rating username').lean();
        if (before) {
          const deduction = Math.min(penaltyRequested, before.rating);
          if (deduction > 0) {
            const applied = await applyRatingDelta(penalizedId, -deduction);
            changes[penaltyColorLetter === 'w' ? 'white' : 'black'] -= Math.abs(applied.applied);
            await recordRatingHistory({
              userId: penalizedId,
              before: applied.before,
              after: applied.after,
              reason: 'match-forfeit',
              detail:
                terminal.reason === 'forfeit'
                  ? `Left the match before it finished (forfeit penalty ${Math.abs(applied.applied)}).`
                  : `Flat penalty (${Math.abs(applied.applied)}).`,
              game: claim._id,
              opponentName: userNameFor(claim, penaltyColorLetter === 'w' ? 'b' : 'w'),
            });
            /* Optionally reward the opponent instead of burning the points. */
            if (FORFEIT_AWARDED) {
              const opponentColor = penaltyColorLetter === 'w' ? 'b' : 'w';
              const opponentId = userIdFor(claim, opponentColor);
              if (opponentId) {
                const awarded = await applyRatingDelta(opponentId, Math.abs(applied.applied));
                changes[opponentColor === 'w' ? 'white' : 'black'] += Math.abs(awarded.applied);
                await recordRatingHistory({
                  userId: opponentId,
                  before: awarded.before,
                  after: awarded.after,
                  reason: 'capture-transfer-win',
                  detail: `Forfeit penalty transferred from ${userNameFor(claim, penaltyColorLetter)}.`,
                  game: claim._id,
                  opponentName: userNameFor(claim, penaltyColorLetter),
                });
              }
            }
            await Game.updateOne(
              { _id: claim._id },
              { $set: { penaltyPoints: deduction, penaltyColor: penaltyColorLetter } }
            );
          }
        }
      }
    }

    await Game.updateOne(
      { _id: claim._id },
      { $set: { ratingChanges: changes, rated, finalized: true } }
    );
  } catch (err) {
    logError('finalizeGame ratings', err);
    await Game.updateOne({ _id: claim._id }, { $set: { rated, finalized: true } }).catch(() => {});
  }

  await releaseSeats(claim._id).catch(() => {});

  const fresh = await Game.findById(claim._id);
  await announceGameResult(fresh);
  return fresh;
}

function winnerDocName(game, winnerColorLetter) {
  return winnerColorLetter === 'w' ? game.whiteName : game.blackName;
}

/** Push the result to both players + persist a notification for each. */
async function announceGameResult(game) {
  if (!game) return;
  let reasonText = String(game.resultReason || '').replace(/-/g, ' ');
  if (game.resultReason === 'timeout-material') {
    reasonText = `time ran out — material advantage ${game.whiteCapturePoints || 0}–${game.blackCapturePoints || 0}`;
  } else if (game.resultReason === 'forfeit') {
    reasonText = 'forfeit (opponent left the match)';
  }
  const summary = game.result === 'draw'
    ? `Draw — ${reasonText}.`
    : `${game.result === 'white' ? game.whiteName : game.blackName} won — ${reasonText}.`;

  for (const color of ['w', 'b']) {
    const uid = userIdFor(game, color);
    if (!uid) continue;
    const delta = color === 'w' ? game.ratingChanges.white : game.ratingChanges.black;
    const sign = delta > 0 ? '+' : '';
    emitToUser(uid, 'game:ended', {
      ...serializeGame(game, uid),
      summary,
      ratingDelta: delta,
    });
    await notifyUser(uid, {
      type: 'game-result',
      title: summary,
      body:
        game.rated && delta !== 0
          ? `Rating change: ${sign}${delta} · ${game.mode === 'ai' ? 'practice game' : 'rated multiplayer game'}.`
          : `${game.mode === 'ai' ? 'Practice game' : 'Rated game'} · no rating change.`,
      meta: { gameId: game.gameId },
    });
  }

  broadcastLiveMatch('live:match:end', game);

  /* Anyone who asked to be told when this player is free again. */
  const waiting = await Invitation.find({
    status: 'pending',
    to: { $in: [game.white, game.black].filter(Boolean) },
    expiresAt: { $gt: new Date() },
  }).lean();
  for (const inv of waiting) {
    emitToUser(inv.from, 'info', {
      message: `${inv.toUsername} is free again — your invitation is still waiting for a reply.`,
    });
  }
}

/** Apply a move for a player (server-authoritative validation). */
async function submitMove({ gameId, userId, from, to, promotion }) {
  return withGameLock(String(gameId), async () => {
    const game = await Game.findOne({ gameId: String(gameId) });
    if (!game) throw fail(404, 'Game not found.', 'game_missing');
    if (game.status !== 'active') throw fail(409, 'This game has already finished.', 'game_finished');

    const color = colorOfPlayer(game, userId);
    if (!color) throw fail(403, 'You are not a player in this match.', 'forbidden');
    if (game.mode === 'ai' && game.aiColor === color) throw fail(400, 'It is the computer\u2019s turn.', 'ai_turn');

    /* The 10-minute match clock is authoritative: a move arriving after the
     * deadline cannot change the result, which is decided on material. */
    if (game.mode === 'multiplayer' && game.clockEndsAt && Date.now() >= new Date(game.clockEndsAt).getTime()) {
      const verdict = materialVerdict(game);
      await finalizeGame(game, { result: verdict.result, reason: verdict.reason });
      throw fail(409, 'Time is up — the match was scored on captured material.', 'time_up');
    }

    const chess = new Chess(game.fen);
    if (chess.turn() !== color) throw fail(400, 'It is not your turn.', 'out_of_turn');

    const fromSq = cleanString(from, 2);
    const toSq = cleanString(to, 2);
    if (!/^[a-h][1-8]$/.test(fromSq) || !/^[a-h][1-8]$/.test(toSq)) {
      throw fail(400, 'Invalid square.', 'bad_square');
    }
    const promo = promotion === 'q' || promotion === 'r' || promotion === 'b' || promotion === 'n' ? promotion : undefined;

    let move = null;
    try {
      move = chess.move({ from: fromSq, to: toSq, promotion: promo });
    } catch (err) {
      move = null;
    }
    if (!move) throw fail(400, 'Illegal move.', 'illegal_move');

    const captureKey = color === 'w' ? 'capturedByWhite' : 'capturedByBlack';
    const pointKey = color === 'w' ? 'whiteCapturePoints' : 'blackCapturePoints';
    const captured = (game[captureKey] || []).slice();
    if (move.captured) captured.push(move.captured);

    const nextPly = game.ply + 1;
    const set = {
      fen: chess.fen(),
      ply: nextPly,
      lastMoveAt: new Date(),
      drawOfferBy: null,
      drawOfferAt: null,
    };
    if (move.captured) {
      set[captureKey] = captured;
      set[pointKey] = capturePoints(captured);
    }

    const moveDoc = {
      ply: nextPly,
      from: move.from,
      to: move.to,
      promotion: move.promotion || null,
      san: move.san,
      color: move.color,
      piece: move.piece,
      captured: move.captured || null,
      fenAfter: chess.fen(),
      playedAt: new Date(),
    };

    /* Optimistic guard on ply: a duplicate or stale move cannot be applied. */
    const updated = await Game.findOneAndUpdate(
      { _id: game._id, status: 'active', ply: game.ply },
      { $set: set, $push: { moves: moveDoc } },
      { returnDocument: 'after' }
    );
    if (!updated) throw fail(409, 'That move was already applied. Board refreshed.', 'stale_move');

    const terminal = terminalState(chess);
    if (terminal) {
      const finished = await finalizeGame(updated, terminal);
      return { game: finished, move: moveDoc, finished: true };
    }

    broadcastGame(updated);
    if (updated.mode === 'ai') scheduleAiReply(updated.gameId);
    return { game: updated, move: moveDoc, finished: false };
  });
}

/** Play one AI move (used for AI games, including the AI's opening move). */
async function playAiMove(gameId) {
  return withGameLock(String(gameId), async () => {
    const game = await Game.findOne({ gameId: String(gameId) });
    if (!game || game.status !== 'active' || game.mode !== 'ai') return null;

    const chess = new Chess(game.fen);
    if (chess.turn() !== game.aiColor) return null;

    const chosen = chooseAiMove(game.fen, game.aiDifficulty || 'medium');
    if (!chosen) {
      const terminal = terminalState(chess) || { result: 'draw', reason: 'stalemate' };
      return finalizeGame(game, terminal);
    }

    chess.move({ from: chosen.from, to: chosen.to, promotion: chosen.promotion });
    const color = game.aiColor;
    const captureKey = color === 'w' ? 'capturedByWhite' : 'capturedByBlack';
    const pointKey = color === 'w' ? 'whiteCapturePoints' : 'blackCapturePoints';
    const captured = (game[captureKey] || []).slice();
    if (chosen.captured) captured.push(chosen.captured);

    const nextPly = game.ply + 1;
    const set = { fen: chess.fen(), ply: nextPly, lastMoveAt: new Date(), drawOfferBy: null, drawOfferAt: null };
    if (chosen.captured) {
      set[captureKey] = captured;
      set[pointKey] = capturePoints(captured);
    }

    const updated = await Game.findOneAndUpdate(
      { _id: game._id, status: 'active', ply: game.ply },
      {
        $set: set,
        $push: {
          moves: {
            ply: nextPly,
            from: chosen.from,
            to: chosen.to,
            promotion: chosen.promotion || null,
            san: chosen.san,
            color,
            piece: chosen.piece,
            captured: chosen.captured || null,
            fenAfter: chess.fen(),
            playedAt: new Date(),
          },
        },
      },
      { returnDocument: 'after' }
    );
    if (!updated) return null;

    const terminal = terminalState(chess);
    if (terminal) return finalizeGame(updated, terminal);
    broadcastGame(updated);
    return updated;
  });
}

const aiTimers = new Map();
function scheduleAiReply(gameId) {
  if (aiTimers.has(gameId)) return;
  const timer = setTimeout(async () => {
    aiTimers.delete(gameId);
    try {
      await playAiMove(gameId);
    } catch (err) {
      logError('ai move', err);
    }
  }, 350);
  timer.unref?.();
  aiTimers.set(gameId, timer);
}

/** Resign (forfeit) — the opponent receives only points they actually captured. */
async function resignGame({ gameId, userId }) {
  return withGameLock(String(gameId), async () => {
    const game = await Game.findOne({ gameId: String(gameId) });
    if (!game) throw fail(404, 'Game not found.', 'game_missing');
    if (game.status !== 'active') throw fail(409, 'This game has already finished.', 'game_finished');
    const color = colorOfPlayer(game, userId);
    if (!color) throw fail(403, 'You are not a player in this match.', 'forbidden');
    if (game.mode === 'ai' && game.aiColor === color) throw fail(400, 'You cannot resign for the computer.', 'forbidden');

    const winner = color === 'w' ? 'black' : 'white';
    return finalizeGame(game, { result: winner, reason: 'resignation' });
  });
}

async function offerOrAnswerDraw({ gameId, userId, accept }) {
  return withGameLock(String(gameId), async () => {
    const game = await Game.findOne({ gameId: String(gameId) });
    if (!game) throw fail(404, 'Game not found.', 'game_missing');
    if (game.status !== 'active') throw fail(409, 'This game has already finished.', 'game_finished');
    const color = colorOfPlayer(game, userId);
    if (!color) throw fail(403, 'You are not a player in this match.', 'forbidden');

    if (accept === undefined) {
      /* Offering a draw. */
      if (game.drawOfferBy === color) return { offered: true, game };
      const updated = await Game.findOneAndUpdate(
        { _id: game._id, status: 'active' },
        { $set: { drawOfferBy: color, drawOfferAt: new Date() } },
        { returnDocument: 'after' }
      );
      if (updated) {
        broadcastGame(updated, { drawOfferMessage: `${userNameFor(updated, color)} offers a draw.` });
        const opponentId = userIdFor(updated, color === 'w' ? 'b' : 'w');
        if (opponentId) {
          await notifyUser(opponentId, {
            type: 'info',
            title: 'Draw offered',
            body: `${userNameFor(updated, color)} offers a draw. Accept or decline from the match panel.`,
            meta: { gameId: updated.gameId },
          });
        }
      }
      return { offered: true, game: updated };
    }

    if (game.drawOfferBy === null || game.drawOfferBy === color) {
      throw fail(400, 'There is no draw offer from your opponent to answer.', 'no_offer');
    }
    if (!accept) {
      const updated = await Game.findOneAndUpdate(
        { _id: game._id, status: 'active', drawOfferBy: game.drawOfferBy },
        { $set: { drawOfferBy: null, drawOfferAt: null } },
        { returnDocument: 'after' }
      );
      if (updated) {
        broadcastGame(updated, { drawDeclined: true });
        const offererId = userIdFor(updated, game.drawOfferBy);
        if (offererId) {
          emitToUser(offererId, 'info', { message: 'Your draw offer was declined.' });
        }
      }
      return { declined: true, game: updated };
    }
    const finished = await finalizeGame(game, { result: 'draw', reason: 'draw-agreed' });
    return { declined: false, game: finished };
  });
}

/**
 * Leave / forfeit an active match.
 *   • PvP : the opponent wins by forfeit and the leaver loses FORFEIT_PENALTY
 *           points (never below 0). The winner still only receives the capture
 *           points they actually earned.
 *   • PvAI: no penalty at all — the practice game is simply closed as abandoned
 *           and can be restarted at any time.
 */
async function leaveGame({ gameId, userId }) {
  return withGameLock(String(gameId), async () => {
    const game = await Game.findOne({ gameId: String(gameId) });
    if (!game) throw fail(404, 'Game not found.', 'game_missing');
    if (game.status !== 'active') throw fail(409, 'That match is already over.', 'game_finished');
    const color = colorOfPlayer(game, userId);
    if (!color) throw fail(403, 'You are not a player in this match.', 'forbidden');
    if (game.mode === 'ai' && game.aiColor === color) throw fail(400, 'You cannot forfeit for the computer.', 'forbidden');

    if (game.mode === 'ai') {
      /* Practice games: leaving is free. */
      const closed = await finalizeGame(game, { result: 'draw', reason: 'abandoned' });
      return { game: closed, penalty: 0, mode: 'ai' };
    }

    const winner = color === 'w' ? 'black' : 'white';
    const closed = await finalizeGame(
      game,
      { result: winner, reason: 'forfeit' },
      { penaltyColor: color, penaltyPoints: FORFEIT_PENALTY }
    );
    return { game: closed, penalty: FORFEIT_PENALTY, mode: 'multiplayer' };
  });
}

/**
 * Resolve every live PvP match whose 10-minute clock has run out.
 * The winner is the side with the higher captured-material score; equal material
 * is a draw. Runs frequently so no match can hang past its deadline.
 */
async function sweepExpiredClocks() {
  try {
    const due = await Game.find({
      status: 'active',
      mode: 'multiplayer',
      clockEndsAt: { $ne: null, $lte: new Date() },
    })
      .select('gameId')
      .limit(20)
      .lean();

    for (const entry of due) {
      await withGameLock(entry.gameId, async () => {
        const fresh = await Game.findOne({ _id: entry._id, status: 'active' });
        if (!fresh) return;
        const verdict = materialVerdict(fresh);
        const closed = await finalizeGame(fresh, { result: verdict.result, reason: verdict.reason });
        if (closed) {
          log(
            `Clock expired: ${closed.gameId} resolved on material ` +
              `${verdict.white}-${verdict.black} → ${closed.result}`
          );
        }
      });
    }
  } catch (err) {
    logError('sweepExpiredClocks', err);
  }
}

/** Timer that forfeits a disconnected PvP player after a grace period. */
const disconnectForfeitTimers = new Map();
const DISCONNECT_GRACE_MS = Math.max(20, Number(process.env.FORFEIT_GRACE_SECONDS ?? 60)) * 1000;

function scheduleDisconnectForfeit(gameId, userId) {
  const key = `${gameId}:${userId}`;
  if (disconnectForfeitTimers.has(key)) return;
  const timer = setTimeout(async () => {
    disconnectForfeitTimers.delete(key);
    try {
      if (presence.has(String(userId))) return; /* they reconnected */
      const game = await Game.findOne({ gameId: String(gameId) }).select('status mode').lean();
      if (!game || game.status !== 'active' || game.mode !== 'multiplayer') return;
      const result = await leaveGame({ gameId, userId });
      emitToUser(userId, 'info', {
        message: `You were forfeited for leaving the match (−${result.penalty} points).`,
      });
    } catch (err) {
      if (!(err && err.expose)) logError('disconnect forfeit', err);
    }
  }, DISCONNECT_GRACE_MS);
  timer.unref?.();
  disconnectForfeitTimers.set(key, timer);
}

function clearDisconnectForfeit(gameId, userId) {
  const key = `${gameId}:${userId}`;
  const timer = disconnectForfeitTimers.get(key);
  if (timer) {
    clearTimeout(timer);
    disconnectForfeitTimers.delete(key);
  }
}

/** Close games that have been idle for too long (no rating transfer). */
const ABANDON_MS = Math.max(5, Number(process.env.ABANDON_MINUTES || 45)) * 60 * 1000;
async function sweepStaleGames() {
  try {
    const cutoff = new Date(Date.now() - ABANDON_MS);
    const stale = await Game.find({
      status: 'active',
      lastMoveAt: { $lt: cutoff },
      /* live PvP games are governed by their 10-minute clock instead */
      $or: [{ mode: 'ai' }, { clockEndsAt: null }],
    }).limit(25);
    for (const game of stale) {
      await withGameLock(game.gameId, async () => {
        const fresh = await Game.findOne({ _id: game._id, status: 'active' });
        if (!fresh) return;
        await finalizeGame(fresh, { result: 'draw', reason: 'abandoned' });
        for (const color of ['w', 'b']) {
          const uid = userIdFor(fresh, color);
          if (uid) emitToUser(uid, 'info', { message: 'The match was closed because no moves were made for a long time. No rating changed.' });
        }
      });
    }
  } catch (err) {
    logError('sweepStaleGames', err);
  }
}

/* ---------------------------------------------------------------------------
 * SECTION 9 — REST API ROUTES
 * ------------------------------------------------------------------------- */

const api = express.Router();
api.use(apiLimiter);

/* ---- helpers ---- */
function findUserByIdentifier(identifier) {
  const value = cleanString(identifier, 254);
  if (!value) return null;
  /* Input is coerced to a plain string before it reaches Mongoose, so no query
   * operators can ever be injected from the request body. */
  return value.includes('@')
    ? User.findOne({ email: value.toLowerCase() })
    : User.findOne({ usernameLower: value.toLowerCase() });
}

function clientConfig() {
  return {
    startRating: START_RATING,
    /* kept for older clients; `declinePenalty` is the new name */
    /* kept for older clients: the declining player pays this, never the inviter */
    rejectPenalty: DECLINE_PENALTY,
    declinePenalty: DECLINE_PENALTY,
    forfeitPenalty: FORFEIT_PENALTY,
    forfeitAwarded: FORFEIT_AWARDED,
    pvpMatchSeconds: PVP_MATCH_SECONDS,
    inviteTtlMs: INVITE_TTL_MS,
    pieceValues: PIECE_VALUES,
    aiRated: AI_GAMES_AFFECT_RATING,
    coachEnabled: Boolean(GROQ_API_KEY),
    aiDifficulties: Object.entries(AI_DIFFICULTIES).map(([key, value]) => ({ key, label: value.label, depth: value.depth })),
  };
}

/* ============================ AUTH ============================ */

api.post(
  '/auth/signup',
  authLimiter,
  requireGuest,
  wrap(async (req, res) => {
    const username = assertUsername(req.body?.username);
    const email = assertEmail(req.body?.email);
    const password = assertPassword(req.body?.password);
    if (typeof req.body?.confirmPassword === 'string' && req.body.confirmPassword !== password) {
      throw fail(400, 'Passwords do not match.', 'password_mismatch');
    }

    /* Reserve the account with the hashed password in a single insert so the
     * unique indexes on usernameLower/email decide races, not a read-then-write. */
    const passwordHash = await bcrypt.hash(password, 12);
    let user;
    try {
      user = await User.create({
        username,
        usernameLower: username.toLowerCase(),
        email,
        passwordHash,
        rating: START_RATING,
        peakRating: START_RATING,
      });
    } catch (err) {
      if (err && err.code === 11000) {
        const field = Object.keys(err.keyPattern || { email: 1 })[0];
        throw fail(409, field === 'email' ? 'That email address is already registered.' : 'That username is already taken.', 'duplicate');
      }
      throw err;
    }

    await recordRatingHistory({
      userId: user._id,
      before: START_RATING,
      after: START_RATING,
      reason: 'registration',
      detail: 'Starting rating assigned on account creation.',
    });

    await establishSession(req, user._id);
    await setOnline(user._id, true);
    /* The token makes the response usable even if the browser refuses the cookie. */
    const token = await issueSessionToken(user._id, req);
    res.status(201).json({ ok: true, user: user.toPublicJSON(), config: clientConfig(), token });
  })
);

api.post(
  '/auth/login',
  authLimiter,
  requireGuest,
  wrap(async (req, res) => {
    const identifier = cleanString(req.body?.identifier ?? req.body?.email ?? req.body?.username, 254);
    const password = typeof req.body?.password === 'string' ? req.body.password : '';
    if (!identifier || !password) throw fail(400, 'Enter your email/username and password.', 'missing_credentials');

    const foundQuery = findUserByIdentifier(identifier);
    const user = foundQuery ? await foundQuery.select('+passwordHash') : null;
    /* Constant-ish work whether or not the account exists, plus a generic error
     * so account existence is never revealed. */
    const hash = user ? user.passwordHash : '$2a$12$0000000000000000000000000000000000000000000000000000';
    const ok = await bcrypt.compare(password, hash).catch(() => false);
    if (!user || !ok) throw fail(401, 'Incorrect credentials. Please try again.', 'invalid_credentials');

    await establishSession(req, user._id);
    await User.updateOne({ _id: user._id }, { $set: { lastActive: new Date() } });
    setOnline(user._id, true).catch(() => {});

    /* If a previous session was left mid-game the client can resume it. */
    const token = await issueSessionToken(user._id, req);
    res.json({
      ok: true,
      user: user.toPublicJSON(),
      activeGameId: user.currentGameId ? String(user.currentGameId) : null,
      config: clientConfig(),
      token,
    });
  })
);

api.post(
  '/auth/logout',
  wrap(async (req, res) => {
    const userId = req.session?.userId;
    if (userId) {
      /* Leaving a live multiplayer game counts as a resignation only if the
       * player explicitly resigns; logging out just frees the seat for resume. */
      await User.updateOne({ _id: userId }, { $set: { lastActive: new Date() } }).catch(() => {});
    }
    const tokenHash = req.session?.tokenHash;
    req.session.destroy(() => {
      res.clearCookie('grandmaster.sid', { path: '/' });
      if (tokenHash) {
        SessionToken.deleteOne({ tokenHash })
          .catch(() => {})
          .then(() => tokenCache.clear());
      }
      res.json({ ok: true });
    });
  })
);

api.get(
  '/auth/me',
  wrap(async (req, res) => {
    if (!req.session?.userId) return res.status(401).json({ error: 'Not signed in.', code: 'unauthenticated' });
    const doc = await User.findById(req.session.userId).select('username rating peakRating wins losses draws gamesPlayed isOnline lastActive currentGameId');
    if (!doc) {
      return req.session.destroy(() => res.status(401).json({ error: 'Not signed in.', code: 'unauthenticated' }));
    }
    const user = doc.toPublicJSON();
    const activeGame = doc.currentGameId ? await Game.findById(doc.currentGameId).select('gameId status').lean() : null;
    res.json({
      user,
      config: clientConfig(),
      activeGameId: activeGame && activeGame.status === 'active' ? activeGame.gameId : null,
    });
  })
);

/* Everything below requires an authenticated session. */
api.use(requireAuth);

/* ============================ LOBBY ============================ */

api.get(
  '/lobby',
  wrap(async (req, res) => {
    const meId = req.session.userId;
    const me = await User.findById(meId);
    if (!me) throw fail(401, 'Account not found. Please sign in again.', 'unauthenticated');
    me.lastActive = new Date();
    await me.save();

    const [online, incoming, outgoing, activeGames, recentGames, leaderboard, history, notes, liveGames] = await Promise.all([
      User.find({ _id: { $ne: me._id }, isOnline: true })
        .select('username rating currentGameId lastActive')
        .sort({ rating: -1 })
        .limit(60)
        .lean(),
      Invitation.find({ to: me._id, status: 'pending', expiresAt: { $gt: new Date() } }).sort({ createdAt: -1 }).lean(),
      Invitation.find({ from: me._id, status: 'pending', expiresAt: { $gt: new Date() } }).sort({ createdAt: -1 }).lean(),
      Game.find({ status: 'active', $or: [{ white: me._id }, { black: me._id }] }).sort({ lastMoveAt: -1 }).lean(),
      Game.find({ status: 'finished', $or: [{ white: me._id }, { black: me._id }] }).sort({ endedAt: -1 }).limit(12).lean(),
      User.find({}).select('username rating wins losses draws').sort({ rating: -1, usernameLower: 1 }).limit(20).lean(),
      RatingHistory.find({ user: me._id }).sort({ createdAt: -1 }).limit(15).lean(),
      Notification.find({ user: me._id }).sort({ createdAt: -1 }).limit(20).lean(),
      Game.find({ status: 'active', mode: 'multiplayer' }).sort({ startedAt: -1 }).limit(12).lean(),
    ]);

    const describeGame = (game) => {
      const youColor = game.white && String(game.white) === String(me._id) ? 'w' : 'b';
      const opponentName = youColor === 'w' ? game.blackName : game.whiteName;
      const opponentId = youColor === 'w' ? game.black : game.white;
      const chess = new Chess(game.fen);
      return {
        gameId: game.gameId,
        mode: game.mode,
        you: youColor,
        opponentName,
        opponentId: opponentId ? String(opponentId) : null,
        opponentRating: youColor === 'w' ? game.blackSnapshot : game.whiteSnapshot,
        turn: chess.turn(),
        ply: game.ply,
        status: game.status,
        aiDifficulty: game.aiDifficulty || null,
        startedAt: game.startedAt,
        endedAt: game.endedAt || null,
        result: game.result || null,
        resultReason: game.resultReason || null,
        ratingDelta: game.ratingChanges ? (youColor === 'w' ? game.ratingChanges.white : game.ratingChanges.black) : 0,
        capturePoints: youColor === 'w' ? game.whiteCapturePoints || 0 : game.blackCapturePoints || 0,
        opponentCapturePoints: youColor === 'w' ? game.blackCapturePoints || 0 : game.whiteCapturePoints || 0,
        moves: (game.moves || []).length,
        lastMoveAt: game.lastMoveAt,
      };
    };

    res.json({
      user: me.toPublicJSON(),
      config: clientConfig(),
      online: online.map((u) => ({
        id: String(u._id),
        username: u.username,
        rating: u.rating,
        inGame: Boolean(u.currentGameId),
        lastActive: u.lastActive,
      })),
      invitations: {
        incoming: incoming.map((inv) => ({
          id: String(inv._id),
          fromId: String(inv.from),
          username: inv.fromUsername,
          rating: inv.fromRating,
          expiresAt: inv.expiresAt,
          createdAt: inv.createdAt,
        })),
        outgoing: outgoing.map((inv) => ({
          id: String(inv._id),
          toId: String(inv.to),
          username: inv.toUsername,
          expiresAt: inv.expiresAt,
          createdAt: inv.createdAt,
        })),
      },
      activeGames: activeGames.map(describeGame),
      recentGames: recentGames.map(describeGame),
      leaderboard: leaderboard.map((u, index) => ({
        rank: index + 1,
        id: String(u._id),
        username: u.username,
        rating: u.rating,
        wins: u.wins,
        losses: u.losses,
        draws: u.draws,
        isMe: String(u._id) === String(me._id),
      })),
      liveMatches: liveGames.map((g) => ({
        gameId: g.gameId,
        white: g.whiteName,
        black: g.blackName,
        whiteRating: g.whiteSnapshot,
        blackRating: g.blackSnapshot,
        moves: (g.moves || []).length,
        capturePoints: { w: g.whiteCapturePoints || 0, b: g.blackCapturePoints || 0 },
        clockEndsAt: g.clockEndsAt || null,
        spectators: spectatorCount(g.gameId),
        isMine: [g.white, g.black].some((id) => id && String(id) === String(me._id)),
      })),
      ratingHistory: history.map((h) => ({
        id: String(h._id),
        previousRating: h.previousRating,
        change: h.change,
        newRating: h.newRating,
        reason: h.reason,
        detail: h.detail,
        opponentName: h.opponentName,
        createdAt: h.createdAt,
      })),
      notifications: notes.map((n) => ({
        id: String(n._id),
        type: n.type,
        title: n.title,
        body: n.body,
        read: n.read,
        createdAt: n.createdAt,
      })),
    });
  })
);

api.post(
  '/notifications/read',
  wrap(async (req, res) => {
    await Notification.updateMany({ user: req.session.userId, read: false }, { $set: { read: true } });
    res.json({ ok: true });
  })
);

/* ========================= INVITATIONS ========================= */

api.post(
  '/invitations',
  inviteLimiter,
  wrap(async (req, res) => {
    const me = await User.findById(req.session.userId);
    if (!me) throw fail(401, 'Please sign in again.', 'unauthenticated');

    const identifier = cleanString(req.body?.toUsername || req.body?.to, 60);
    if (!identifier) throw fail(400, 'Choose a player to invite.', 'no_target');

    const targetQuery = findUserByIdentifier(identifier);
    const target = targetQuery ? await targetQuery : null;
    if (!target) throw fail(404, 'No player found with that username.', 'not_found');
    if (String(target._id) === String(me._id)) throw fail(400, 'You cannot invite yourself.', 'self_invite');

    /* Mutual invitation → accept immediately, it is what both players want. */
    const reverse = await Invitation.findOne({ from: target._id, to: me._id, status: 'pending', expiresAt: { $gt: new Date() } });
    if (reverse) {
      const claimed = await Invitation.findOneAndUpdate(
        { _id: reverse._id, status: 'pending' },
        { $set: { status: 'accepted', respondedAt: new Date() } },
        { returnDocument: 'after' }
      );
      if (claimed) {
        try {
          const game = await startMultiplayerGame(claimed.from, claimed.to);
          await Invitation.updateOne({ _id: claimed._id }, { $set: { gameId: game._id } });
          await onGameStarted(game, { invitationId: claimed._id });
          return res.json({ ok: true, autoAccepted: true, gameId: game.gameId });
        } catch (err) {
          await Invitation.updateOne({ _id: claimed._id }, { $set: { status: 'pending' } }).catch(() => {});
          throw err;
        }
      }
    }

    if (me.currentGameId) {
      throw fail(409, 'Finish your active match before inviting someone new.', 'self_busy');
    }
    if (target.currentGameId) {
      const active = await Game.findById(target.currentGameId).select('whiteName blackName white').lean();
      let partner = 'another player';
      if (active) {
        partner = String(active.white) === String(target._id) ? active.blackName : active.whiteName;
      }
      await notifyUser(me._id, {
        type: 'busy',
        title: 'Player is in a match',
        body: `${target.username} is currently playing a match with ${partner}.`,
        meta: { playerId: String(target._id) },
      });
      throw fail(409, `${target.username} is currently playing a match with ${partner}.`, 'opponent_busy');
    }

    const existing = await Invitation.findOne({ from: me._id, to: target._id, status: 'pending' });
    if (existing) {
      return res.json({ ok: true, invitation: { id: String(existing._id), expiresAt: existing.expiresAt }, duplicate: true });
    }

    let invitation;
    try {
      invitation = await Invitation.create({
        from: me._id,
        to: target._id,
        fromUsername: me.username,
        toUsername: target.username,
        fromRating: me.rating,
        status: 'pending',
        expiresAt: new Date(Date.now() + INVITE_TTL_MS),
      });
    } catch (err) {
      if (err && err.code === 11000) {
        throw fail(409, 'You already have a pending invitation to that player.', 'duplicate');
      }
      throw err;
    }

    emitToUser(target._id, 'invitation:new', {
      id: String(invitation._id),
      fromId: String(me._id),
      username: me.username,
      rating: me.rating,
      expiresAt: invitation.expiresAt,
    });
    await notifyUser(target._id, {
      type: 'invitation',
      title: 'New challenge',
      body: `${me.username} (${me.rating}) invited you to a rated match.`,
      meta: { invitationId: String(invitation._id) },
    });

    res.status(201).json({
      ok: true,
      invitation: { id: String(invitation._id), toUsername: target.username, expiresAt: invitation.expiresAt },
    });
  })
);

api.post(
  '/invitations/:id/cancel',
  wrap(async (req, res) => {
    const id = toObjectId(req.params.id);
    if (!id) throw fail(400, 'Invalid invitation.', 'bad_id');
    const claimed = await Invitation.findOneAndUpdate(
      { _id: id, from: req.session.userId, status: 'pending' },
      { $set: { status: 'cancelled', respondedAt: new Date() } },
      { returnDocument: 'after' }
    );
    if (!claimed) throw fail(404, 'That invitation is no longer pending.', 'not_pending');
    /* Expired/cancelled invitations never apply the decline penalty. */
    emitToUser(claimed.to, 'invitation:update', { id: String(claimed._id), status: 'cancelled' });
    res.json({ ok: true });
  })
);

api.post(
  '/invitations/:id/respond',
  inviteLimiter,
  wrap(async (req, res) => {
    const id = toObjectId(req.params.id);
    if (!id) throw fail(400, 'Invalid invitation.', 'bad_id');
    const action = req.body?.action === 'accept' ? 'accept' : req.body?.action === 'reject' ? 'reject' : null;
    if (!action) throw fail(400, 'Choose accept or reject.', 'bad_action');

    /* Atomic claim: only the first responder wins, duplicates are no-ops. */
    const claimed = await Invitation.findOneAndUpdate(
      { _id: id, to: req.session.userId, status: 'pending', expiresAt: { $gt: new Date() } },
      { $set: { status: action === 'accept' ? 'accepted' : 'rejected', respondedAt: new Date() } },
      { returnDocument: 'after' }
    );
    if (!claimed) {
      const existing = await Invitation.findById(id).lean();
      if (!existing) throw fail(404, 'Invitation not found.', 'not_found');
      if (existing.status === 'pending') throw fail(409, 'That invitation has expired.', 'expired');
      throw fail(409, 'That invitation has already been answered.', 'already_answered');
    }

    if (action === 'accept') {
      try {
        const game = await startMultiplayerGame(claimed.from, claimed.to);
        await Invitation.updateOne({ _id: claimed._id }, { $set: { gameId: game._id } });
        await onGameStarted(game, { invitationId: claimed._id });
        return res.json({ ok: true, gameId: game.gameId, accepted: true });
      } catch (err) {
        await Invitation.updateOne({ _id: claimed._id }, { $set: { status: 'cancelled' } }).catch(() => {});
        emitToUser(claimed.from, 'invitation:update', { id: String(claimed._id), status: 'cancelled' });
        throw err;
      }
    }

    /* ---------------- DECLINE: the INVITED player forfeits 10 points --------
     * The inviter is never charged. `penaltyApplied` is flipped with an atomic
     * update first, so refreshes, duplicate REST/socket calls and races can
     * never charge the same decline twice. If the decliner has fewer than 10
     * points only what they own is deducted (ratings never go negative). */
    const penaltyClaim = await Invitation.findOneAndUpdate(
      { _id: claimed._id, penaltyApplied: false },
      { $set: { penaltyApplied: true } },
      { returnDocument: 'after' }
    );
    if (!penaltyClaim) {
      return res.json({ ok: true, rejected: true, declined: true, penalty: 0, note: 'Penalty already applied.' });
    }

    const decliner = await User.findById(claimed.to).select('rating username').lean();
    let penalty = 0;
    let newRating = decliner ? decliner.rating : 0;
    if (decliner) {
      const requested = Math.min(DECLINE_PENALTY, decliner.rating);
      const result =
        requested > 0
          ? await applyRatingDelta(decliner._id, -requested)
          : { before: decliner.rating, after: decliner.rating, applied: 0 };
      penalty = Math.abs(result.applied);
      newRating = result.after;
      if (penalty > 0) {
        await recordRatingHistory({
          userId: decliner._id,
          before: result.before,
          after: result.after,
          reason: 'invitation-rejected',
          detail: `Declined ${claimed.fromUsername}'s invitation (decline penalty ${penalty}).`,
          invitation: claimed._id,
          opponentName: claimed.fromUsername,
        });
      }
      await Invitation.updateOne({ _id: claimed._id }, { $set: { penaltyAmount: penalty } });
      emitToUser(decliner._id, 'rating:update', { rating: newRating, change: -penalty, reason: 'invitation-rejected' });
    }

    /* Tell the inviter their challenge was declined — with no penalty for them. */
    emitToUser(claimed.from, 'invitation:update', {
      id: String(claimed._id),
      status: 'rejected',
      penalty: 0,
      username: claimed.toUsername,
      declinePenalty: penalty,
      newRating,
    });
    await notifyUser(claimed.from, {
      type: 'invitation-rejected',
      title: 'Invitation declined',
      body: `${claimed.toUsername} declined your challenge. No points were deducted from you.`,
      meta: { invitationId: String(claimed._id), penalty: 0 },
    });

    res.json({ ok: true, rejected: true, declined: true, penalty, penaltyOwner: 'decliner' });
  })
);

/* ============================ GAMES ============================ */

/** Shared post-start wiring: notify, broadcast, expire the invitation. */
async function onGameStarted(game, { invitationId } = {}) {
  for (const color of ['w', 'b']) {
    const uid = userIdFor(game, color);
    if (!uid) continue;
    const opponent = userNameFor(game, color === 'w' ? 'b' : 'w');
    emitToUser(uid, 'game:start', {
      gameId: game.gameId,
      you: color,
      opponentName: opponent,
      mode: game.mode,
      opponentRating: color === 'w' ? game.blackSnapshot : game.whiteSnapshot,
    });
    await notifyUser(uid, {
      type: 'invitation-accepted',
      title: 'Your match is ready',
      body: `You are playing ${color === 'w' ? 'White' : 'Black'} against ${opponent}. Capture points decide the rating transfer.`,
      meta: { gameId: game.gameId, invitationId: invitationId ? String(invitationId) : null },
    });
  }
  if (io) {
    for (const color of ['w', 'b']) {
      const uid = userIdFor(game, color);
      if (uid) socketsForUser(uid).forEach((sid) => io.sockets.sockets.get(sid)?.join(gameRoomByGameId(game.gameId)));
    }
    /* Every online user hears about a new live PvP match. */
    if (game.mode === 'multiplayer') broadcastLiveMatch('live:match:start', game);
  }
  return game;
}

api.post(
  '/games/ai',
  wrap(async (req, res) => {
    const difficulty = cleanString(req.body?.difficulty, 12) || 'medium';
    const color = req.body?.color === 'w' || req.body?.color === 'b' ? req.body.color : 'random';
    const game = await startAiGame(req.session.userId, difficulty, color === 'random' ? undefined : color);
    await onGameStarted(game, {});
    if (game.aiColor === 'w') scheduleAiReply(game.gameId);
    res.status(201).json({ ok: true, gameId: game.gameId, game: serializeGame(game, req.session.userId) });
  })
);

api.get(
  '/games/:gameId',
  wrap(async (req, res) => {
    const game = await Game.findOne({ gameId: cleanString(req.params.gameId, 64) });
    if (!game) throw fail(404, 'Game not found.', 'game_missing');
    const color = colorOfPlayer(game, req.session.userId);
    if (!color) throw fail(403, 'You are not a player in this match.', 'forbidden');
    res.json({ game: serializeGame(game, req.session.userId) });
  })
);

api.get(
  '/games/:gameId/spectate',
  wrap(async (req, res) => {
    const game = await Game.findOne({ gameId: cleanString(req.params.gameId, 64) });
    if (!game) throw fail(404, 'Match not found.', 'game_missing');
    if (game.mode !== 'multiplayer') throw fail(400, 'Only live PvP matches can be watched.', 'not_watchable');
    res.json({ game: spectateState(game), canChat: Boolean(colorOfPlayer(game, req.session.userId)) });
  })
);

api.post(
  '/games/:gameId/leave',
  wrap(async (req, res) => {
    const game = await Game.findOne({ gameId: cleanString(req.params.gameId, 64) });
    if (!game) throw fail(404, 'Game not found.', 'game_missing');
    const result = await leaveGame({ gameId: game.gameId, userId: req.session.userId });
    res.json({ ok: true, penalty: result.penalty, mode: result.mode });
  })
);

api.get(
  '/live',
  wrap(async (req, res) => {
    const games = await Game.find({ status: 'active', mode: 'multiplayer' })
      .sort({ startedAt: -1 })
      .limit(20)
      .lean();
    res.json({
      matches: games.map((g) => ({
        gameId: g.gameId,
        white: g.whiteName,
        black: g.blackName,
        whiteRating: g.whiteSnapshot,
        blackRating: g.blackSnapshot,
        moves: (g.moves || []).length,
        capturePoints: { w: g.whiteCapturePoints || 0, b: g.blackCapturePoints || 0 },
        clockEndsAt: g.clockEndsAt || null,
        spectators: spectatorCount(g.gameId),
        isMine: [g.white, g.black].some((id) => id && String(id) === String(req.session.userId)),
      })),
    });
  })
);

api.get(
  '/games',
  wrap(async (req, res) => {
    const games = await Game.find({ status: 'active', $or: [{ white: req.session.userId }, { black: req.session.userId }] })
      .sort({ lastMoveAt: -1 })
      .limit(10);
    res.json({ games: games.map((g) => serializeGame(g, req.session.userId)) });
  })
);

/* ======================== OPTIONAL AI COACH ======================== */

api.post(
  '/coach',
  coachLimiter,
  wrap(async (req, res) => {
    if (!GROQ_API_KEY) {
      throw fail(503, 'The coach is not configured on this server (set GROQ_API_KEY).', 'coach_disabled');
    }
    const question = cleanString(req.body?.question, 600);
    const fen = cleanString(req.body?.fen, 120);
    if (!question) throw fail(400, 'Ask a question first.', 'no_question');
    let legal = '';
    try {
      const chess = new Chess(fen || undefined);
      legal = chess.moves({ verbose: true }).slice(0, 24).map((m) => m.san).join(' ');
    } catch (err) {
      legal = '';
    }

    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 20000);
    try {
      const response = await fetch('https://api.groq.com/openai/v1/chat/completions', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', Authorization: `Bearer ${GROQ_API_KEY}` },
        signal: controller.signal,
        body: JSON.stringify({
          model: GROQ_MODEL,
          temperature: 0.5,
          max_tokens: 320,
          messages: [
            {
              role: 'system',
              content:
                'You are a concise, encouraging chess coach. Use algebraic notation. Never claim to have run an engine. Keep answers under 130 words.',
            },
            {
              role: 'user',
              content: `Position FEN: ${fen}\nLegal moves (sample): ${legal}\nQuestion: ${question}`,
            },
          ],
        }),
      });
      const data = await response.json().catch(() => null);
      if (!response.ok) throw fail(502, data?.error?.message || 'Coach service error.', 'coach_error');
      const answer = data?.choices?.[0]?.message?.content;
      if (!answer) throw fail(502, 'The coach returned an empty answer.', 'coach_empty');
      res.json({ answer });
    } catch (err) {
      if (err.name === 'AbortError') throw fail(504, 'The coach took too long to answer.', 'coach_timeout');
      throw err;
    } finally {
      clearTimeout(timeout);
    }
  })
);

/* ---- pieces (single source of truth for the artwork) ---- */
app.get('/api/pieces/:color/:type.svg', (req, res) => {
  const { color, type } = req.params;
  const svg = buildPieceSvg(color, type);
  if (!svg) return res.status(404).end();
  res.type('image/svg+xml').set('Cache-Control', 'public, max-age=604800, immutable').send(svg);
});

/* Unknown /api/* paths answer with JSON 404 (never the HTML shell, never a
 * misleading 401 from the auth guard). Registered last so every real route wins. */
api.use((req, res) => {
  res.status(404).json({ error: `Endpoint ${req.method} ${req.originalUrl} not found.`, code: 'not_found' });
});

app.use('/api', api);

/* ---- Health probe (no auth, no secrets) ---- */
app.get('/healthz', (req, res) => {
  res.json({
    ok: mongoose.connection.readyState === 1,
    db: mongoose.connection.readyState === 1 ? 'connected' : 'disconnected',
    uptime: Math.round(process.uptime()),
  });
});

/* ---------------------------------------------------------------------------
 * SECTION 10 — SOCKET.IO (session-sharing auth, presence, matchmaking, play)
 * ------------------------------------------------------------------------- */

io = new SocketServer(server, {
  maxHttpBufferSize: 64 * 1024,
  pingInterval: 25000,
  pingTimeout: 20000,
  /* Same-origin app: credentials travel with the session cookie. */
  cors: { origin: true, credentials: true },
});

/* Share the exact same express-session with Socket.IO handshakes. */
io.engine.use(sessionMiddleware);

io.use(
  wrap(async (socket, next) => {
    const sess = socket.request.session;
    let userId = sess && sess.userId ? String(sess.userId) : null;

    /* Cookie-less clients authenticate the socket with the same bearer token
     * they use for HTTP (handshake `auth.token` or an `x-gm-token` header). */
    if (!userId) {
      const handshake = socket.handshake || {};
      const raw = cleanString(
        (handshake.auth && (handshake.auth.token || handshake.auth['x-gm-token'])) ||
          (handshake.headers && handshake.headers['x-gm-token']) ||
          '',
        200
      );
      if (raw) userId = await resolveSessionToken(raw);
    }
    if (!userId) return next(new Error('unauthenticated'));

    const user = await User.findById(userId).select('username rating currentGameId');
    if (!user) return next(new Error('unauthenticated'));
    socket.data.userId = String(user._id);
    socket.data.username = user.username;
    return next();
  })
);

/** Uniform ack-based handler wrapper for socket events. */
function socketHandler(handler) {
  return async (payload, ack) => {
    const respond = typeof ack === 'function' ? ack : () => {};
    try {
      const result = (await handler(payload || {})) || {};
      respond({ ok: true, ...result });
    } catch (err) {
      if (err && err.expose) {
        respond({ ok: false, error: err.message, code: err.code || 'error' });
      } else {
        logError(`socket ${err?.stack ? err.stack.split('\n')[0] : err}`, err);
        respond({ ok: false, error: 'Something went wrong. Please try again.', code: 'internal' });
      }
    }
  };
}

/* ---- Matchmaking queue ---- */
const matchQueue = new Map(); // userId -> { userId, socketId, username, rating, joinedAt }

function removeFromQueue(userId) {
  matchQueue.delete(String(userId));
}

async function tryPairMatch(userId) {
  const me = matchQueue.get(String(userId));
  if (!me) return;
  const candidates = Array.from(matchQueue.values()).filter((entry) => entry.userId !== me.userId);
  if (!candidates.length) {
    emitToUser(me.userId, 'matchmaking:waiting', { queuePosition: matchQueue.size });
    return;
  }
  /* Prefer the closest rating; widen the bracket the longer someone waits. */
  candidates.sort((a, b) => {
    const dw = Math.abs(a.rating - me.rating) - Math.abs(b.rating - me.rating);
    return dw !== 0 ? dw : a.joinedAt - b.joinedAt;
  });
  const best = candidates[0];
  const waitedLong = Date.now() - me.joinedAt > 20000 || Date.now() - best.joinedAt > 20000;
  if (!waitedLong && Math.abs(best.rating - me.rating) > 250) {
    emitToUser(me.userId, 'matchmaking:waiting', { queuePosition: matchQueue.size });
    return;
  }

  removeFromQueue(me.userId);
  removeFromQueue(best.userId);
  try {
    const game = await startMultiplayerGame(me.userId, best.userId);
    await onGameStarted(game, {});
    emitToUser(me.userId, 'matchmaking:matched', { gameId: game.gameId });
    emitToUser(best.userId, 'matchmaking:matched', { gameId: game.gameId });
  } catch (err) {
    logError('matchmaking', err);
    emitToUser(me.userId, 'matchmaking:cancelled', {
      reason: err.expose ? err.message : 'Matchmaking failed. Please try again.',
    });
    emitToUser(best.userId, 'matchmaking:cancelled', {
      reason: err.expose ? err.message : 'Matchmaking failed. Please try again.',
    });
  }
}

/** Load a game for a socket user, asserting participation. */
async function loadGameForUser(gameId, userId) {
  const game = await Game.findOne({ gameId: String(gameId || '') });
  if (!game) throw fail(404, 'Game not found.', 'game_missing');
  const color = colorOfPlayer(game, userId);
  if (!color) throw fail(403, 'You are not a player in this match.', 'forbidden');
  return { game, color };
}

io.on('connection', (socket) => {
  const userId = socket.data.userId;
  const sid = socket.id;

  (async () => {
    let set = presence.get(userId);
    const wasEmpty = !set || set.size === 0;
    if (!set) {
      set = new Set();
      presence.set(userId, set);
    }
    set.add(sid);
    socket.join(userRoom(userId));

    if (wasEmpty) await setOnline(userId, true).catch(() => {});

    /* Reconnected before the grace period ended — cancel any pending forfeit. */
    try {
      const me = await User.findById(userId).select('currentGameId').lean();
      if (me && me.currentGameId) {
        const game = await Game.findById(me.currentGameId).select('gameId').lean();
        if (game) clearDisconnectForfeit(game.gameId, userId);
      }
    } catch (err) {
      logError('clear forfeit timer', err);
    }

    /* Send the current online roster to the newly connected tab. */
    try {
      const online = await User.find({ isOnline: true, _id: { $ne: userId } })
        .select('username rating currentGameId')
        .sort({ rating: -1 })
        .limit(60)
        .lean();
      socket.emit('presence:list', {
        online: online.map((u) => ({
          id: String(u._id),
          username: u.username,
          rating: u.rating,
          inGame: Boolean(u.currentGameId),
        })),
      });
    } catch (err) {
      logError('presence list', err);
    }

    /* Rejoin the room of an active game so refreshes resume seamlessly. */
    try {
      const me = await User.findById(userId).select('currentGameId').lean();
      if (me?.currentGameId) {
        const game = await Game.findById(me.currentGameId);
        if (game && game.status === 'active') {
          socket.join(gameRoomByGameId(game.gameId));
          socket.emit('game:state', serializeGame(game, userId));
        }
      }
    } catch (err) {
      logError('socket resume', err);
    }
  })();

  socket.on('presence:ping', socketHandler(async () => {
    await User.updateOne({ _id: userId }, { $set: { lastActive: new Date() } });
    return { pong: Date.now() };
  }));

  socket.on('game:join', socketHandler(async ({ gameId }) => {
    const { game } = await loadGameForUser(gameId, userId);
    socket.join(gameRoomByGameId(game.gameId));
    return { game: serializeGame(game, userId) };
  }));

  socket.on('game:move', socketHandler(async ({ gameId, from, to, promotion }) => {
    const { game } = await loadGameForUser(gameId, userId);
    const result = await submitMove({ gameId: game.gameId, userId, from, to, promotion });
    return { finish: result.finished };
  }));

  socket.on('game:resign', socketHandler(async ({ gameId }) => {
    const { game } = await loadGameForUser(gameId, userId);
    await resignGame({ gameId: game.gameId, userId });
    return { resigned: true };
  }));

  socket.on('game:draw:offer', socketHandler(async ({ gameId }) => {
    const { game } = await loadGameForUser(gameId, userId);
    const result = await offerOrAnswerDraw({ gameId: game.gameId, userId });
    return { offered: true, drawOfferBy: result.game ? result.game.drawOfferBy : null };
  }));

  socket.on('game:draw:respond', socketHandler(async ({ gameId, accept }) => {
    const { game } = await loadGameForUser(gameId, userId);
    const result = await offerOrAnswerDraw({ gameId: game.gameId, userId, accept: Boolean(accept) });
    return { accepted: Boolean(accept), finished: result.game ? result.game.status === 'finished' : false };
  }));

  socket.on('game:leave', socketHandler(async ({ gameId }) => {
    const { game } = await loadGameForUser(gameId, userId);
    const result = await leaveGame({ gameId: game.gameId, userId });
    return { left: true, penalty: result.penalty, mode: result.mode };
  }));

  /* ---------------------------- spectating ---------------------------- */
  socket.on('spectate:join', socketHandler(async ({ gameId }) => {
    const game = await Game.findOne({ gameId: String(gameId || '') });
    if (!game) throw fail(404, 'Match not found.', 'game_missing');
    if (game.mode !== 'multiplayer') throw fail(400, 'Only live PvP matches can be watched.', 'not_watchable');
    if (game.status !== 'active') throw fail(409, 'That match has already finished.', 'game_finished');
    /* Players get their own board view, not the audience one. */
    if (colorOfPlayer(game, userId)) throw fail(400, 'You are a player in this match — open its board instead.', 'is_player');

    socket.join(spectatorRoom(game.gameId));
    socket.data.spectating = game.gameId;
    broadcastSpectatorCount(game.gameId);
    return { game: spectateState(game) };
  }));

  socket.on('spectate:leave', socketHandler(async ({ gameId }) => {
    const id = String(gameId || socket.data.spectating || '');
    if (id) {
      socket.leave(spectatorRoom(id));
      socket.data.spectating = null;
      broadcastSpectatorCount(id);
    }
    return { left: true };
  }));

  /* ------------------- audience commentary (never board input) ------------- */
  socket.on('game:chat', socketHandler(async ({ gameId, text }) => {
    const game = await Game.findOne({ gameId: String(gameId || '') });
    if (!game) throw fail(404, 'Match not found.', 'game_missing');
    if (game.status !== 'active') throw fail(409, 'This match has finished.', 'game_finished');

    const asPlayer = colorOfPlayer(game, userId);
    const canWatch = Boolean(socket.rooms.has(spectatorRoom(game.gameId)));
    if (!asPlayer && !canWatch) throw fail(403, 'Open the match to join the conversation.', 'not_watching');

    const now = Date.now();
    if (socket.data.lastChatAt && now - socket.data.lastChatAt < 1200) {
      throw fail(429, 'Take a breath — one message every second.', 'chat_rate');
    }
    const clean = cleanString(text, 240);
    if (!clean) throw fail(400, 'Write something first.', 'empty_chat');
    socket.data.lastChatAt = now;

    const entry = {
      username: socket.data.username,
      role: asPlayer ? 'player' : 'spectator',
      text: clean,
      at: new Date(),
    };
    await Game.updateOne(
      { _id: game._id },
      { $push: { spectatorChat: { $each: [entry], $slice: -80 } } }
    );

    const payload = {
      gameId: game.gameId,
      username: entry.username,
      role: entry.role,
      text: entry.text,
      at: entry.at,
    };
    io.to(spectatorRoom(game.gameId)).emit('game:chat', payload);
    for (const color of ['w', 'b']) {
      const uid = userIdFor(game, color);
      if (uid) emitToUser(uid, 'game:chat', payload);
    }
    return { sent: true };
  }));

  socket.on('matchmaking:join', socketHandler(async () => {
    const me = await User.findById(userId).select('currentGameId username rating').lean();
    if (!me) throw fail(401, 'Account not found.', 'unauthenticated');
    if (me.currentGameId) throw fail(409, 'You are already in an active match.', 'busy');

    matchQueue.set(userId, {
      userId,
      socketId: sid,
      username: me.username,
      rating: me.rating,
      joinedAt: Date.now(),
    });
    setImmediate(() => {
      tryPairMatch(userId).catch((err) => logError('matchmaking pair', err));
    });
    return { queued: true, queuePosition: matchQueue.size };
  }));

  socket.on('matchmaking:leave', socketHandler(async () => {
    removeFromQueue(userId);
    return { queuePosition: 0 };
  }));

  socket.on('disconnect', () => {
    removeFromQueue(userId);
    if (socket.data.spectating) broadcastSpectatorCount(socket.data.spectating);
    const set = presence.get(userId);
    if (!set) return;
    set.delete(sid);
    if (set.size === 0) {
      presence.delete(userId);
      /* Only now is the account offline — NOT when one tab closes. */
      setOnline(userId, false).catch(() => {});

      /* A player who vanishes from an active PvP match forfeits after a short
       * grace period (they may simply be refreshing). AI games never expire. */
      User.findById(userId)
        .select('currentGameId')
        .lean()
        .then(async (me) => {
          if (!me || !me.currentGameId) return;
          const game = await Game.findById(me.currentGameId).select('gameId mode status').lean();
          if (game && game.status === 'active' && game.mode === 'multiplayer') {
            scheduleDisconnectForfeit(game.gameId, userId);
          }
        })
        .catch(() => {});
    }
  });
});

/* ---- Invitation expiry sweep (no penalty for expiry) ---- */
async function sweepInvitations() {
  try {
    const expired = await Invitation.find({ status: 'pending', expiresAt: { $lte: new Date() } }).limit(50).lean();
    for (const inv of expired) {
      const claimed = await Invitation.findOneAndUpdate(
        { _id: inv._id, status: 'pending' },
        { $set: { status: 'expired', respondedAt: new Date() } },
        { returnDocument: 'after' }
      );
      if (!claimed) continue;
      emitToUser(claimed.from, 'invitation:update', { id: String(claimed._id), status: 'expired' });
      emitToUser(claimed.to, 'invitation:update', { id: String(claimed._id), status: 'expired' });
    }
  } catch (err) {
    logError('sweepInvitations', err);
  }
}

const invitationSweeper = setInterval(sweepInvitations, 15000);
const clockSweeper = setInterval(sweepExpiredClocks, 3000);
const gameSweeper = setInterval(sweepStaleGames, 5 * 60 * 1000);
const presenceJanitor = setInterval(async () => {
  /* Safety net: if a socket died without a disconnect event, reconcile presence. */
  try {
    const users = await User.find({ isOnline: true }).select('_id').lean();
    for (const u of users) {
      if (!presence.has(String(u._id))) await setOnline(u._id, false);
    }
  } catch (err) {
    logError('presence janitor', err);
  }
}, 60 * 1000);
for (const t of [invitationSweeper, gameSweeper, presenceJanitor, clockSweeper]) t.unref?.();

/* ---------------------------------------------------------------------------
 * SECTION 11 — EMBEDDED FRONTEND (HTML + CSS + browser JavaScript)
 * Served straight from this file. No other application source files exist.
 * ------------------------------------------------------------------------- */

const APP_CSS = `:root{
  color-scheme:light;
  --bg:#f1f6f5; --bg-2:#e8f1ef;
  --panel:#ffffff; --panel-2:#f6faf9; --panel-3:#eaf3f1;
  --surface:#ffffff; --surface-2:#f4f8f7; --surface-3:#e3efec;
  --line:#d9e7e4; --line-soft:#e6f0ee; --line-strong:#bcd6d1;
  --ink:#0d2b29; --ink-2:#2c514e; --ivory:#0d2b29;
  --muted:#5d7d7a; --muted-2:#7f9c99;
  --teal:#008080; --teal-strong:#006b6b; --teal-deep:#005858;
  --teal-soft:#d9f0ee; --teal-soft-2:#eef8f7; --teal-line:#a8d8d3;
  --gold:#0b6b69; --gold-bright:#00605f; --gold-dim:#8ab8b3;
  --emerald:#008080; --emerald-bright:#0a9a92;
  --danger:#c23b2b; --danger-soft:#fdecea; --danger-line:#e8b4ac;
  --warn:#8a6a12; --warn-soft:#fdf4dd; --warn-line:#e6d09a;
  --sq-light:#eef4f2; --sq-dark:#5b9d95;
  --radius:0; --radius-sm:0;
  --shadow-lg:none; --shadow-md:none; --shadow-sm:none;
  /* ---- type system -------------------------------------------------------
     Playfair Display : brand, headlines, names, big ratings
     Merriweather     : body copy, chat, move list, notes (reading text)
     Poppins          : UI chrome — buttons, labels, pills, tables, statuses
     Libre Baskerville: numerals, quotes, the Baskerville voice of the app */
  --font-display:"Playfair Display","Libre Baskerville","Baskerville","Baskerville Old Face","Hoefler Text",Georgia,"Times New Roman",serif;
  --font-serif:"Merriweather",Georgia,"Times New Roman",serif;
  --font-baskerville:"Libre Baskerville","Baskerville","Baskerville Old Face","Hoefler Text",Georgia,"Times New Roman",serif;
  --font-sans:"Poppins",ui-sans-serif,system-ui,-apple-system,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;
  --font-mono:"Poppins",ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  /* legacy aliases kept so every existing rule upgrades in one go */
  --serif:var(--font-display);
  --sans:var(--font-sans);
  --mono:var(--font-mono);
  --grid-line:rgba(0,128,128,.055);
}
*{box-sizing:border-box}
[hidden]{display:none!important}
html,body{margin:0;padding:0;min-height:100%}
body{
  background-color:var(--bg);
  background-image:
    radial-gradient(1200px 640px at 10% -12%, rgba(0,128,128,.075), transparent 62%),
    radial-gradient(900px 520px at 92% 4%, rgba(0,128,128,.05), transparent 60%),
    linear-gradient(180deg,#f4f9f8 0%,rgba(241,246,245,0) 46%,#eef5f3 100%);
  background-attachment:fixed;
  color:var(--ink);
  font:400 14.5px/1.72 var(--font-serif);
  font-feature-settings:"kern" 1,"liga" 1;
  -webkit-font-smoothing:antialiased; text-rendering:optimizeLegibility;
}
button,input,select,textarea{font:inherit;color:inherit}
button{cursor:pointer}
button:disabled{cursor:not-allowed;opacity:.5}
a{color:var(--teal-strong);text-decoration:none;border-bottom:1px solid var(--teal-line)}
a:hover{border-bottom-color:var(--teal)}
h1,h2,h3,h4{font-family:var(--font-display);font-weight:600;letter-spacing:-.01em;margin:0;color:var(--ink);font-feature-settings:"kern" 1,"liga" 1}
p{margin:0 0 10px}
p:last-child{margin-bottom:0}
strong,b{font-weight:700}
/* every interactive chrome element speaks Poppins */
button,input,select,textarea,.btn,.pill,.seg button,.status,.clock,.hint,.tiny,.field label,
.spec-pill,.countdown,.coord,.capscore,.tag,.ring-card h4,.chat-form,.toast,.dialog-actions,.gameactions{
  font-family:var(--font-sans);
}
/* numerals and quotes get the Baskerville voice */
.rating-hero .big,.stat b,.scorecard b,.result-banner .delta,.rating-tag,.lb-row .rank,.clock,
.ring-rating,.member-since,.nav-meta,.delta-pos,.delta-neg,.delta-zero,.capscore,.countdown{
  font-family:var(--font-baskerville);
  font-variant-numeric:tabular-nums lining-nums;
  font-feature-settings:"tnum" 1,"lnum" 1;
}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-track{background:transparent}
::-webkit-scrollbar-thumb{background:#c6dad6;border:2px solid var(--bg)}
::-webkit-scrollbar-thumb:hover{background:#aac7c1}
::selection{background:var(--teal-soft);color:var(--teal-deep)}
.view{animation:fade .2s ease both}
.splash{min-height:100dvh;display:grid;place-items:center;background:var(--bg)}
@keyframes fade{from{opacity:0}to{opacity:1}}
@media (prefers-reduced-motion:reduce){*{animation-duration:.001s!important;transition-duration:.001s!important}}

/* ---------- shared primitives ---------- */
.btn{
  border:1px solid var(--teal); background:var(--teal);
  color:#ffffff; border-radius:0; padding:11px 18px; font-family:var(--font-sans);
  font-weight:600; font-size:13px; letter-spacing:.02em;
  transition:background .14s,border-color .14s,color .14s;
  display:inline-flex; align-items:center; justify-content:center; gap:8px; white-space:nowrap;
}
.btn:hover:not(:disabled){background:var(--teal-strong);border-color:var(--teal-strong)}
.btn:active:not(:disabled){background:var(--teal-deep);border-color:var(--teal-deep)}
.btn:focus-visible,select:focus-visible,input:focus-visible,textarea:focus-visible,.square:focus-visible,.btn.ghost:focus-visible{
  outline:2px solid var(--teal);outline-offset:2px;
}
.btn.primary{background:var(--teal);border-color:var(--teal);color:#fff}
.btn.primary:hover:not(:disabled){background:var(--teal-strong);border-color:var(--teal-strong)}
.btn.emerald{background:var(--teal-strong);border-color:var(--teal-strong);color:#fff}
.btn.emerald:hover:not(:disabled){background:var(--teal-deep);border-color:var(--teal-deep)}
.btn.ghost{background:#fff;border-color:var(--line-strong);color:var(--ink-2)}
.btn.ghost:hover:not(:disabled){background:var(--teal-soft-2);border-color:var(--teal);color:var(--teal-deep)}
.btn.danger{background:#fff;border-color:var(--danger-line);color:var(--danger)}
.btn.danger:hover:not(:disabled){background:var(--danger-soft);border-color:var(--danger);color:#a02c1e}
.btn.sm{padding:7px 12px;font-size:12.5px}
.btn.block{width:100%}
.btn.icon{padding:9px;min-width:38px}
.card{
  background:var(--surface);
  border:1px solid var(--line); border-radius:0; padding:16px 17px;
}
.card h3{font-family:var(--font-sans);font-size:11px;letter-spacing:.18em;text-transform:uppercase;color:var(--teal-strong);margin-bottom:14px;display:flex;align-items:center;gap:8px;justify-content:space-between;font-weight:700}
.card h3 .hint{font:500 10.5px/1.3 var(--font-sans);letter-spacing:.02em;text-transform:none;color:var(--muted-2)}
.empty{color:var(--muted-2);font:400 italic 12.5px/1.6 var(--font-serif);padding:12px 10px;border:1px dashed var(--line);text-align:center;background:var(--surface-2)}
.pill{display:inline-flex;align-items:center;gap:6px;padding:4px 10px;border-radius:0;font-family:var(--font-sans);font-size:10px;font-weight:700;letter-spacing:.1em;text-transform:uppercase;border:1px solid var(--line-strong);color:var(--muted);background:#fff}
.pill.gold{border-color:var(--teal-line);color:var(--teal-strong);background:var(--teal-soft-2)}
.pill.live{border-color:var(--teal-line);color:var(--teal-strong);background:var(--teal-soft)}
.pill.off{border-color:var(--line-strong);color:var(--muted-2);background:var(--surface-2)}
.pill.win{border-color:var(--teal-line);color:var(--teal-strong);background:var(--teal-soft)}
.pill.loss{border-color:var(--danger-line);color:var(--danger);background:var(--danger-soft)}
.pill.draw{border-color:var(--line-strong);color:var(--muted);background:var(--surface-2)}
.dot{width:7px;height:7px;border-radius:50%;background:var(--teal);box-shadow:none;flex:none}
.dot.busy{background:#c9931f}
.dot.off{background:#b7c9c6}
.muted{color:var(--muted)}
.tiny{font-size:11.5px}
.mono{font-variant-numeric:tabular-nums}
.row{display:flex;align-items:center;gap:10px}
.between{display:flex;align-items:center;justify-content:space-between;gap:10px}
.stack{display:grid;gap:10px}
.divider{height:1px;background:var(--line-soft);margin:12px 0}

/* ---------- auth ---------- */
.auth-view{min-height:100vh;display:grid;grid-template-columns:1.02fr .98fr;align-items:stretch;background:var(--bg)}
.auth-art{
  position:relative;padding:56px clamp(28px,5vw,72px);display:flex;flex-direction:column;justify-content:center;gap:26px;
  background:var(--teal-soft-2);border-right:1px solid var(--line);overflow:hidden;
}
.auth-art .ghost-piece{position:absolute;right:-60px;bottom:-90px;width:min(58%,520px);opacity:.10;pointer-events:none}
.auth-brand{display:flex;align-items:center;gap:14px}
.auth-mark{width:52px;height:52px;border-radius:0;border:1px solid var(--teal-line);background:#fff;display:grid;place-items:center;overflow:hidden}
.auth-mark img{width:44px;height:44px}
.auth-brand h1{font-family:var(--serif);font-size:26px;letter-spacing:.14em;color:var(--teal-deep);font-weight:600}
.auth-brand span{display:block;font:10.5px/1 var(--sans);letter-spacing:.3em;color:var(--muted);text-transform:uppercase;margin-top:7px}
.auth-art h2{font-family:var(--font-display);font-weight:600;font-size:clamp(30px,3.4vw,48px);line-height:1.1;max-width:15ch;letter-spacing:-.02em;color:var(--ink)}
.auth-art h2 em{font-style:normal;color:var(--teal)}
.auth-art p{max-width:46ch;color:var(--ink-2);font-family:var(--font-serif);font-size:14px;line-height:1.8;margin:0}
.auth-features{display:grid;gap:12px;max-width:46ch;margin-top:4px}
.auth-feature{display:flex;gap:11px;font-family:var(--font-sans);font-size:12.5px;line-height:1.6;color:var(--ink-2)}
.auth-feature b{color:var(--ink);font-weight:650}
.auth-feature .ico{width:26px;height:26px;flex:none;border-radius:0;border:1px solid var(--teal-line);display:grid;place-items:center;background:#fff;color:var(--teal-strong);font-size:13px}
.auth-panel{display:grid;place-items:center;padding:34px clamp(20px,4vw,54px);background:var(--bg)}
.auth-card{width:min(100%,430px);background:#fff;border:1px solid var(--line);border-radius:0;padding:26px 26px 22px}
.auth-tabs{display:grid;grid-template-columns:1fr 1fr;gap:0;background:var(--surface-2);border:1px solid var(--line);border-radius:0;padding:0;margin-bottom:20px}
.auth-tabs button{background:transparent;border:0;border-radius:0;padding:11px 10px;font-family:var(--font-sans);font-size:12.5px;font-weight:600;letter-spacing:.02em;color:var(--muted);transition:background .16s,color .16s;border-bottom:2px solid transparent}
.auth-tabs button.active{background:#fff;color:var(--teal-strong);border-bottom-color:var(--teal)}
.field{display:block;margin-bottom:13px}
.field label{display:block;font-family:var(--font-sans);font-size:10.5px;font-weight:600;letter-spacing:.12em;text-transform:uppercase;color:var(--muted);margin-bottom:7px}
.field input,.field select,.input{
  width:100%;background:#fff;border:1px solid var(--line-strong);border-radius:0;padding:11px 13px;
  color:var(--ink);font-family:var(--font-sans);font-size:13.5px;transition:border-color .14s,box-shadow .14s;
}
.field input::placeholder,.input::placeholder{color:#9db5b1}
.field input:focus,.field select:focus,.input:focus{border-color:var(--teal);box-shadow:0 0 0 3px var(--teal-soft);outline:none}
.form-msg{min-height:18px;font-family:var(--font-sans);font-size:12px;margin:2px 0 10px;color:var(--danger)}
.form-msg.ok{color:var(--teal-strong)}
.fine-print{font-family:var(--font-serif);font-size:11.5px;color:var(--muted-2);line-height:1.75;margin:14px 0 0;border-top:1px solid var(--line-soft);padding-top:12px}

/* ---------- top bar ---------- */
.topbar{
  position:sticky;top:0;z-index:40;display:flex;align-items:center;justify-content:space-between;gap:14px;
  padding:11px clamp(12px,2.2vw,26px);border-bottom:1px solid var(--line);background:#fff;
}
.brand-small{display:flex;align-items:center;gap:11px;min-width:0}
.brand-small .auth-mark{width:38px;height:38px;flex:none;border-radius:0}
.brand-small .auth-mark img{width:32px;height:32px}
.brand-small strong{display:block;font-family:var(--font-display);font-size:16px;letter-spacing:.14em;color:var(--teal-deep);font-weight:600}
.brand-small small{display:block;font-family:var(--font-sans);font-size:9px;letter-spacing:.26em;text-transform:uppercase;color:var(--muted-2);margin-top:3px;font-weight:500}
.topbar-right{display:flex;align-items:center;gap:9px;flex-wrap:wrap;justify-content:flex-end}
.userchip{display:flex;align-items:center;gap:9px;border:1px solid var(--line);border-radius:0;padding:4px 12px 4px 4px;background:var(--surface-2)}
.avatar{width:30px;height:30px;border-radius:50%;display:grid;place-items:center;font-weight:700;font-size:12.5px;color:#fff;background:var(--teal);letter-spacing:.02em;flex:none}
.userchip .uname{display:block;font-family:var(--font-sans);font-size:12.5px;font-weight:600;line-height:1.15;color:var(--ink)}
.userchip .urating{display:block;font-family:var(--font-baskerville);font-size:10.5px;color:var(--teal-strong);font-variant-numeric:tabular-nums lining-nums;margin-top:2px}

/* ---------- lobby ---------- */
.lobby{max-width:1560px;margin:0 auto;padding:18px clamp(12px,2.2vw,26px) 60px;display:grid;grid-template-columns:1.05fr 1.1fr .9fr;gap:16px;align-items:start}
.lobby .col{display:grid;gap:16px;min-width:0}
.statgrid{display:grid;grid-template-columns:repeat(4,1fr);gap:0;margin-top:13px;border:1px solid var(--line)}
.stat{background:#fff;border-right:1px solid var(--line);border-radius:0;padding:11px 8px;text-align:center}
.stat:last-child{border-right:0}
.stat b{display:block;font-size:21px;font-family:var(--font-baskerville);color:var(--ink);font-variant-numeric:tabular-nums lining-nums;font-weight:700;letter-spacing:-.01em}
.stat span{display:block;font-family:var(--font-sans);font-size:9px;font-weight:600;letter-spacing:.16em;text-transform:uppercase;color:var(--muted-2);margin-top:5px}
.rating-hero{display:flex;align-items:flex-end;gap:12px;margin-top:2px}
.rating-hero .big{font-family:var(--font-display);font-size:46px;line-height:1;color:var(--teal);font-variant-numeric:tabular-nums lining-nums;font-weight:600;letter-spacing:-.02em}
.rating-hero .lbl{font-family:var(--font-sans);font-size:10px;font-weight:600;letter-spacing:.18em;text-transform:uppercase;color:var(--muted-2);padding-bottom:7px;line-height:1.5}
.rules-note{margin-top:14px;font-family:var(--font-serif);font-size:11.5px;line-height:1.8;color:var(--ink-2);background:var(--teal-soft-2);border:1px solid var(--teal-line);border-left:3px solid var(--teal);border-radius:0;padding:10px 12px}
.rules-note b{color:var(--teal-deep)}
.seg{display:grid;grid-template-columns:repeat(3,1fr);gap:0;background:var(--surface-2);border:1px solid var(--line);border-radius:0;padding:0;margin-bottom:12px}
.seg button{background:transparent;border:0;border-right:1px solid var(--line);border-radius:0;padding:10px 4px;font-family:var(--font-sans);font-size:11.5px;font-weight:600;letter-spacing:.03em;color:var(--muted)}
.seg button:last-child{border-right:0}
.seg button.active{background:var(--teal);color:#fff}
.playgrid{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:10px}
.list{display:grid;gap:8px;max-height:330px;overflow:auto;padding-right:2px}
.list-row{display:flex;align-items:center;justify-content:space-between;gap:9px;padding:9px 10px;border:1px solid var(--line);border-radius:0;background:#fff;transition:border-color .14s,background .14s}
.list-row:hover{border-color:var(--teal-line);background:var(--teal-soft-2)}
.list-row .who{min-width:0}
.list-row .who b{display:block;font-family:var(--font-sans);font-size:12.5px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;color:var(--ink)}
.list-row .who span{font-family:var(--font-sans);font-size:10.5px;color:var(--muted-2)}
.list-row .who .me-tag{color:var(--teal-strong);font-weight:700}
.rating-tag{font-family:var(--font-baskerville);font-size:13.5px;color:var(--teal-strong);font-variant-numeric:tabular-nums lining-nums;font-weight:700}
.invite-row{display:grid;grid-template-columns:1fr auto auto;gap:7px;align-items:center;padding:9px 10px;border:1px solid var(--teal-line);border-left:3px solid var(--teal);border-radius:0;background:var(--teal-soft-2)}
.countdown{font-size:11px;color:var(--teal-strong);font-variant-numeric:tabular-nums}
.note-list{display:grid;gap:0;max-height:260px;overflow:auto;border:1px solid var(--line)}
.note-item{border-bottom:1px solid var(--line-soft);border-left:2px solid var(--line-strong);padding:8px 10px;background:#fff}
.note-item:last-child{border-bottom:0}
.note-item b{display:block;font-family:var(--font-sans);font-size:12px;font-weight:600;color:var(--ink);letter-spacing:.01em}
.note-item span{font-family:var(--font-serif);font-size:11.5px;line-height:1.65;color:var(--muted-2)}
.note-item.unread{border-left-color:var(--teal);background:var(--teal-soft-2)}
.lb-row{display:grid;grid-template-columns:24px 1fr auto;gap:9px;align-items:center;padding:7px 8px;border-radius:0;font-size:13px;border-bottom:1px solid var(--line-soft)}
.lb-row:last-child{border-bottom:0}
.lb-row.me{background:var(--teal-soft);border-left:3px solid var(--teal)}
.lb-row .rank{font-family:var(--font-baskerville);color:var(--muted-2);text-align:right;font-variant-numeric:tabular-nums}
.lb-row .nm{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.hist-row{display:grid;grid-template-columns:1fr auto;gap:8px;align-items:center;padding:9px 2px;border-bottom:1px solid var(--line-soft);font-family:var(--font-sans);font-size:12px}
.hist-row:last-child{border-bottom:0}
.delta-pos{color:var(--teal-strong);font-variant-numeric:tabular-nums;font-weight:700}
.delta-neg{color:var(--danger);font-variant-numeric:tabular-nums;font-weight:700}
.delta-zero{color:var(--muted-2);font-variant-numeric:tabular-nums}

/* ---------- game view ---------- */
.gamewrap{max-width:1780px;margin:0 auto;padding:10px clamp(10px,2vw,28px) 16px;display:grid;grid-template-columns:minmax(0,1fr) 380px;gap:20px;align-items:start}
@media (min-width:1100px){
  #viewGame .gamewrap{grid-template-columns:minmax(0,1fr) 400px;column-gap:22px;row-gap:12px;
    grid-template-rows:auto auto minmax(0,1fr)}
  #viewGame .boardcol{display:contents}
  #viewGame .board-frame{grid-column:1;grid-row:1/span 3;align-self:start;justify-self:center;
    width:min(100%,calc(100dvh - 124px),1080px);margin:0}
  #viewGame .matchdeck{grid-column:2;grid-row:1}
  #viewGame .sidepanel{grid-column:2;grid-row:2;margin-top:0}
  #viewGame #spectatorBanner{grid-column:2;grid-row:1}
  #viewGame .matchdeck .playerbar{min-height:52px;padding:8px 13px}
  #viewGame .matchdeck .playerbar .who b{font-size:16px}
  #viewGame .matchdeck .playerbar .avatar{width:32px;height:32px}
}
.boardcol{min-width:0;display:flex;flex-direction:column;align-items:center;gap:9px}
.matchdeck{display:flex;flex-direction:column;gap:8px;width:100%;min-width:0}
.board-foot{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-top:9px;padding-top:8px;border-top:1px solid var(--line-soft)}
.board-foot #frameMeta{font-family:var(--font-sans);font-size:9.5px;font-weight:600;letter-spacing:.22em;text-transform:uppercase;color:var(--muted-2)}
.frame-dots{display:inline-flex;gap:5px}
.frame-dots i{width:6px;height:6px;border-radius:50%;background:var(--teal-line);display:block}
.frame-dots i:first-child{background:var(--teal);box-shadow:0 0 8px rgba(0,128,128,.8)}
.board-frame{
  position:relative;width:min(100%,calc(100dvh - 250px),1050px);min-width:260px;margin:0 auto;
  background-color:#ffffff;
  background-image:
    linear-gradient(90deg,var(--teal) 0%,var(--teal) 34%,#38c3b6 50%,var(--teal) 66%,var(--teal) 100%),
    linear-gradient(180deg,#ffffff,#f7fbfa 70%,#eef6f4);
  background-repeat:no-repeat,no-repeat;
  background-size:100% 3px,100% 100%;
  background-position:top left,top left;
  border:1px solid var(--line-strong);padding:13px 13px 12px;
  box-shadow:0 1px 0 0 rgba(255,255,255,.9) inset,0 24px 48px -34px rgba(0,88,88,.55);
}
/* corner brackets — the "digital frame" look */
.board-frame::before,.board-frame::after{
  content:"";position:absolute;width:20px;height:20px;pointer-events:none;z-index:5;
  border:2px solid var(--teal);opacity:.8;
}
.board-frame::before{left:-6px;top:-6px;border-right:0;border-bottom:0}
.board-frame::after{right:-6px;bottom:-6px;border-left:0;border-top:0}
.playerbar{display:flex;align-items:center;justify-content:space-between;gap:10px;background:#fff;border:1px solid var(--line);border-radius:0;padding:5px 11px;min-height:44px;transition:border-color .15s,box-shadow .15s}
.playerbar.active{border-color:var(--teal-line);background:linear-gradient(180deg,#f3fbfa,#eaf6f4);box-shadow:inset 4px 0 0 var(--teal)}
.playerbar .who{display:flex;align-items:center;gap:9px;min-width:0}
.playerbar .who b{font-family:var(--font-display);font-size:15px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:46vw;color:var(--ink)}
.playerbar .who .pr{font-family:var(--font-baskerville);font-size:11px;color:var(--teal-strong);font-variant-numeric:tabular-nums;letter-spacing:.02em}
.captured{display:flex;flex-wrap:wrap;justify-content:flex-end;align-items:center;min-height:22px;gap:0}
.captured img{width:23px;height:23px;margin-left:-8px}
.captured .capscore{font-size:12px;color:var(--teal-strong);margin-left:9px;font-variant-numeric:tabular-nums;font-weight:700}
.board-shell{position:relative;margin:0}
.board-shell::before,.board-shell::after{content:"";position:absolute;inset:0;pointer-events:none;z-index:4}
.board-shell::after{
  background-image:
    repeating-linear-gradient(to right,rgba(0,74,68,.05) 0 1px,transparent 1px 12.5%),
    repeating-linear-gradient(to bottom,rgba(0,74,68,.05) 0 1px,transparent 1px 12.5%);
  mix-blend-mode:multiply;
}
.board-shell::before{box-shadow:inset 0 0 52px -18px rgba(0,64,58,.38)}
.board{
  display:grid;grid-template-columns:repeat(8,1fr);aspect-ratio:1/1;width:100%;
  border:1px solid var(--teal-line);border-radius:0;overflow:hidden;
  touch-action:manipulation;background:var(--sq-light);
  box-shadow:0 0 0 1px rgba(255,255,255,.85) inset,0 14px 30px -22px rgba(0,88,88,.6);
}
.square{
  position:relative;display:grid;place-items:center;border:0;border-radius:0;padding:0;min-width:0;
  aspect-ratio:1;transition:filter .12s,box-shadow .12s;
  box-shadow:inset 0 0 0 .5px rgba(0,72,66,.10);
}
.square.light{background-color:#f4faf9;background-image:linear-gradient(160deg,#f7fcfa,#e8f1ef)}
.square.dark{background-color:#51988f;background-image:linear-gradient(160deg,#5aa79d,#3f8b82)}
.square:hover{filter:brightness(1.05)}
.square:not(.readonly):active{filter:brightness(.98)}
.square.last::before,.square.selected::before,.square.check::before,.square.hint::after{content:"";position:absolute;inset:0;pointer-events:none}
.square.last::before{background:rgba(0,150,140,.26);box-shadow:inset 0 0 0 1px rgba(0,128,128,.4)}
.square.selected::before{background:rgba(0,128,128,.22);box-shadow:inset 0 0 0 3px var(--teal),inset 0 0 22px -6px rgba(0,128,128,.75),0 0 0 3px rgba(0,128,128,.18)}
.square.check::before{background:radial-gradient(circle,rgba(194,59,43,.78),rgba(194,59,43,.24) 62%,transparent 78%)}
.square.hint::after{box-shadow:inset 0 0 0 3px rgba(0,128,128,.6)}
.square:focus-visible{outline:3px solid var(--teal-deep);outline-offset:-3px;z-index:4}
.piece{position:relative;width:96%;height:96%;z-index:2;object-fit:contain;pointer-events:none;
  filter:drop-shadow(0 2px 2px rgba(6,44,40,.35)) drop-shadow(0 0 1px rgba(255,255,255,.25));transition:transform .12s ease}
.square:hover .piece{transform:translateY(-1px) scale(1.015)}
.legal{position:absolute;border-radius:50%;width:22%;height:22%;background:rgba(0,128,128,.6);z-index:3;pointer-events:none;
  box-shadow:0 0 0 5px rgba(0,128,128,.12),0 0 14px -2px rgba(0,128,128,.7)}
.legal.capture{width:86%;height:86%;background:none;border:3px solid rgba(0,128,128,.7);
  box-shadow:0 0 0 3px rgba(0,128,128,.14),inset 0 0 16px -6px rgba(0,128,128,.8)}
.coord{position:absolute;z-index:3;font-family:var(--font-sans);font-size:clamp(8px,1.05vw,11px);font-weight:600;
  letter-spacing:.06em;pointer-events:none;opacity:.9;text-transform:uppercase}
.light .coord{color:#4f7f78}.dark .coord{color:#f2fdfa}
.coord.rank{top:3px;left:4px}.coord.file{right:4px;bottom:2px}
.status{width:min(100%,1050px);margin:7px auto 0;text-align:center;padding:8px 13px;font-family:var(--font-sans);font-size:13px;letter-spacing:.02em;background:#fff;border:1px solid var(--line);border-left:3px solid var(--teal);border-radius:0;font-size:13px;color:var(--ink-2);min-height:40px;display:grid;place-items:center}
.status.alert{color:var(--danger);border-color:var(--danger-line);border-left-color:var(--danger);background:var(--danger-soft)}
.status.win{color:var(--teal-deep);border-color:var(--teal-line);border-left-color:var(--teal);background:var(--teal-soft-2)}
.status::before{
  content:"";width:6px;height:6px;border-radius:50%;background:var(--teal);
  box-shadow:0 0 0 3px rgba(0,128,128,.16);animation:statusPulse 2.1s ease-in-out infinite;
  position:absolute;left:12px;top:50%;margin-top:-3px;
}
#status{position:relative}
@keyframes statusPulse{0%,100%{opacity:1}50%{opacity:.3}}
.gameactions{display:grid;grid-template-columns:repeat(auto-fit,minmax(112px,1fr));gap:8px;width:min(100%,1050px);margin:6px auto 0}
.sidepanel{display:grid;gap:12px;min-width:0}
.scorebox{display:grid;grid-template-columns:1fr 1fr;gap:0;border:1px solid var(--line);background:#fff}
.scorecard{background:#fff;border-right:1px solid var(--line);border-radius:0;padding:10px 12px}
.scorecard:last-child{border-right:0}
.scorecard b{display:block;font-family:var(--font-baskerville);font-size:27px;color:var(--teal);font-variant-numeric:tabular-nums lining-nums;line-height:1.1;font-weight:700}
.scorecard span{font-family:var(--font-sans);font-size:9.5px;font-weight:600;letter-spacing:.15em;text-transform:uppercase;color:var(--muted-2)}
.movelist{max-height:min(42vh,360px);overflow:auto;font-variant-numeric:tabular-nums;border:1px solid var(--line)}
.move-row{display:grid;grid-template-columns:34px 1fr 1fr;gap:4px;padding:6px 8px;border-radius:0;
  font-family:var(--font-serif);font-size:12.5px;border-bottom:1px solid var(--line-soft)}
.move-row:nth-child(even){background:var(--surface-2)}
.move-row .num{color:var(--muted-2)}
.move-row .san{font-family:var(--font-sans);font-weight:600;font-size:12px;letter-spacing:.02em;color:var(--ink)}
.move-row .san.last{color:var(--teal-strong)}
.offer-banner{border:1px solid var(--teal-line);border-left:3px solid var(--teal);background:var(--teal-soft-2);border-radius:0;padding:11px 12px;display:grid;gap:9px}
.offer-banner .row2{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.coach-box{display:grid;gap:9px}
.coach-log{max-height:190px;overflow:auto;display:grid;gap:8px;font-size:12.5px;line-height:1.6}
.coach-msg{padding:9px 11px;border-radius:0;background:var(--surface-2);border:1px solid var(--line);white-space:pre-wrap;overflow-wrap:anywhere;color:var(--ink-2);font-family:var(--font-serif);font-size:12px;line-height:1.7}
.coach-msg.user{background:var(--teal-soft);border-color:var(--teal-line);justify-self:end;max-width:92%}
.coach-form{display:grid;grid-template-columns:1fr auto;gap:7px}
.coach-form input{width:100%;background:#fff;border:1px solid var(--line-strong);border-radius:0;padding:9px 11px;font-size:12.5px}

/* ---------- dialogs, toasts ---------- */
dialog{
  width:calc(100% - 32px);max-width:440px;background:#fff;color:var(--ink);
  border:1px solid var(--line-strong);border-radius:0;padding:22px;
}
dialog::backdrop{background:rgba(13,43,41,.42)}
dialog h2{font-family:var(--font-display);font-size:22px;font-weight:600;color:var(--ink);margin-bottom:10px}
dialog p{color:var(--ink-2);font-family:var(--font-serif);font-size:13px;line-height:1.75;margin:0 0 8px}
.dialog-actions{display:flex;justify-content:flex-end;gap:9px;margin-top:20px;flex-wrap:wrap}
.promo{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-top:14px}
.promo button{background:var(--surface-2);border:1px solid var(--line-strong);border-radius:0;padding:8px;transition:border-color .14s,background .14s}
.promo button:hover{border-color:var(--teal);background:var(--teal-soft-2)}
.promo img{width:100%;height:auto;display:block}
.toasts{position:fixed;right:16px;bottom:16px;z-index:100;display:grid;gap:8px;max-width:min(92vw,360px)}
.toast{
  background:#fff;border:1px solid var(--line);border-left:3px solid var(--teal);
  border-radius:0;padding:11px 13px;animation:toastIn .2s ease both;font-size:13px;
}
.toast b{display:block;font-family:var(--font-sans);font-size:12px;font-weight:600;margin-bottom:3px;color:var(--ink)}
.toast span{color:var(--muted);font-family:var(--font-serif);font-size:11.5px;line-height:1.6}
.toast.error{border-left-color:var(--danger);background:var(--danger-soft)}
.toast.success{border-left-color:var(--teal)}
.toast.info{border-left-color:var(--teal);background:var(--teal-soft-2)}
@keyframes toastIn{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:none}}
.result-banner{border:1px solid var(--teal-line);border-left:3px solid var(--teal);border-radius:0;padding:14px;background:var(--teal-soft-2);display:grid;gap:6px}
.result-banner h4{font-family:var(--font-display);font-size:19px;font-weight:600;color:var(--teal-deep)}
.result-banner .delta{font-family:var(--font-baskerville);font-size:27px;font-variant-numeric:tabular-nums;font-weight:700;color:var(--ink)}

/* ---------- live match clock ---------- */
.clock{font-family:var(--font-baskerville);font-weight:700;font-size:14px;line-height:1;font-variant-numeric:tabular-nums lining-nums;
  letter-spacing:.06em;padding:7px 11px;border-radius:0;border:1px solid var(--teal-line);
  background:linear-gradient(180deg,#f2fbfa,#e6f5f2);color:var(--teal-deep);
  box-shadow:0 0 0 1px rgba(255,255,255,.8) inset,0 0 16px -8px rgba(0,128,128,.85)}
.clock.low{border-color:var(--danger-line);background:var(--danger-soft);color:var(--danger);animation:clockPulse 1s steps(2,end) infinite}
@keyframes clockPulse{50%{opacity:.5}}

/* ---------- incoming challenge: call-style popup ---------- */
.ringpop{position:fixed;inset:0;z-index:80;display:grid;place-items:center;padding:18px;background:rgba(13,43,41,.42)}
.ring-card{width:min(370px,100%);border-radius:0;border:1px solid var(--line-strong);border-top:3px solid var(--teal);background:#fff;padding:22px 20px 18px;text-align:center;position:relative;overflow:hidden}
.ring-avatar{width:72px;height:72px;margin:8px auto 14px;border-radius:50%;display:grid;place-items:center;font:600 28px var(--serif);color:#fff;background:var(--teal);position:relative}
.ring-avatar::before,.ring-avatar::after{content:"";position:absolute;inset:-9px;border-radius:50%;border:2px solid rgba(0,128,128,.45);animation:ringWave 1.9s ease-out infinite}
.ring-avatar::after{border-color:rgba(0,128,128,.24);animation-delay:.65s}
@keyframes ringWave{0%{transform:scale(.88);opacity:.9}100%{transform:scale(1.5);opacity:0}}
.ring-card h4{font-family:var(--font-sans);font-weight:700;font-size:10px;line-height:1.4;letter-spacing:.22em;text-transform:uppercase;color:var(--teal-strong);margin:0 0 6px}
.ring-name{font-family:var(--font-display);font-size:22px;font-weight:600;color:var(--ink)}
.ring-rating{font-size:11.5px;color:var(--muted);margin-top:3px;font-variant-numeric:tabular-nums}
.ring-note{font-family:var(--font-serif);font-size:11.5px;color:var(--ink-2);background:var(--surface-2);border:1px solid var(--line);border-radius:0;padding:10px 12px;margin:14px 0 0;text-align:left;line-height:1.75}
.ring-note b{color:var(--danger)}
.ring-actions{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:14px}
.ring-actions .btn{padding:12px 10px;font-size:13.5px}
.ring-decline{background:#fff;border-color:var(--danger-line);color:var(--danger)}
.ring-decline:hover:not(:disabled){background:var(--danger-soft);border-color:var(--danger)}
.ring-count{font-family:var(--font-sans);font-size:10.5px;color:var(--muted-2);margin-top:10px;font-variant-numeric:tabular-nums;letter-spacing:.04em}
@media (prefers-reduced-motion:reduce){.ring-avatar::before,.ring-avatar::after{animation:none}}

/* ---------- live matches / spectating ---------- */
.live-row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:9px 10px;border:1px solid var(--line);border-radius:0;background:#fff;margin-bottom:8px}
.live-row:hover{border-color:var(--teal-line)}
.live-row .vs{font-size:12.5px;line-height:1.4;min-width:0}
.live-row .vs b{display:block;font-family:var(--font-sans);font-size:12.5px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;color:var(--ink)}
.live-row .vs span{font-family:var(--font-sans);color:var(--muted-2);font-size:10.5px}
.live-row .meta{display:flex;align-items:center;gap:7px;flex-shrink:0}
.spec-pill{display:inline-flex;align-items:center;gap:5px;font-family:var(--font-sans);font-size:9.5px;font-weight:700;letter-spacing:.12em;letter-spacing:.07em;text-transform:uppercase;color:var(--teal-strong);border:1px solid var(--teal-line);background:var(--teal-soft);border-radius:0;padding:3px 8px}
.board.readonly .square{cursor:default}
.board.readonly .square:hover{filter:none}
.spectator-banner{display:flex;align-items:center;gap:9px;flex-wrap:wrap;border:1px solid var(--teal-line);border-left:3px solid var(--teal);background:var(--teal-soft-2);color:var(--ink-2);border-radius:0;padding:10px 13px;font-family:var(--font-sans);font-size:12px;margin-bottom:10px;width:min(100%,1050px);margin-left:auto;margin-right:auto}
.spectator-banner b{color:var(--teal-deep)}

/* ---------- match chat ---------- */
.chat-log{display:flex;flex-direction:column;gap:6px;max-height:210px;overflow-y:auto;margin-bottom:9px;padding:8px;border:1px solid var(--line);background:var(--surface-2)}
.chat-msg{font-family:var(--font-serif);font-size:12px;line-height:1.65;border:1px solid var(--line);border-radius:0;background:#fff;padding:7px 10px;word-break:break-word;color:var(--ink-2)}
.chat-msg b{font-family:var(--font-sans);font-size:11.5px;color:var(--teal-deep);font-weight:600;letter-spacing:.01em}
.chat-msg .tag{font-size:9px;letter-spacing:.1em;text-transform:uppercase;color:var(--teal-strong);background:var(--teal-soft);border:1px solid var(--teal-line);border-radius:0;padding:1px 6px;margin-left:6px;vertical-align:1px}
.chat-msg.spectator{border-left:2px solid var(--teal)}
.chat-msg.mine{background:var(--teal-soft-2);border-color:var(--teal-line)}
.chat-msg.system{color:var(--muted);font-style:italic;background:transparent;border-style:dashed}
.chat-form{display:flex;gap:8px}
.chat-form .input{flex:1;min-width:0}

/* ---------- responsive ---------- */
#viewGame .topbar{min-height:0;padding:7px clamp(10px,2vw,28px);gap:10px}
#viewGame .topbar .clock{padding:5px 9px}
#viewGame .playerbar .avatar{width:28px;height:28px}
@media (max-width:1500px){
  .board-frame{width:min(100%,calc(100dvh - 194px),1000px)}
}
@media (max-width:1099px){
  #viewGame .boardcol{display:flex;flex-direction:column;gap:9px;align-items:stretch}
  #viewGame .matchdeck{display:contents}
  #viewGame #topBar{order:0}
  #viewGame .board-frame{order:1;width:min(100%,calc(100dvh - 300px),860px);margin:0 auto}
  #viewGame #bottomBar{order:2}
  #viewGame #spectatorBanner{order:3}
  #viewGame #status{order:4}
  #viewGame #playerActions{order:5}
  #viewGame #spectatorActions{order:6}
  #viewGame #topBar,#viewGame #bottomBar{width:min(100%,860px);margin:0 auto}
}
@media (max-width:1200px){
  .lobby{grid-template-columns:1fr 1fr}
  .gamewrap{grid-template-columns:minmax(0,1fr) 340px;gap:16px}
}
@media (max-width:940px){
  .auth-view{grid-template-columns:1fr}
  .auth-art{padding:32px 22px 22px;border-right:0;border-bottom:1px solid var(--line)}
  .auth-art h2{font-size:29px;max-width:22ch}
  .auth-art .ghost-piece{display:none}
  .auth-features{display:none}
  .auth-panel{padding:24px 18px 40px}
  .lobby{grid-template-columns:1fr}
  .gamewrap{grid-template-columns:1fr}
  .board-frame{width:min(100%,calc(100dvh - 186px),800px)}
  .sidepanel{order:2}
}
@media (max-width:620px){
  .topbar{padding:8px 9px;gap:6px}
  .topbar-right{gap:5px;flex-wrap:nowrap;flex:0 0 auto}
  #btnSound{display:none}
  #connPill,#gameConn{display:none}
  #btnLogout{font-size:11px;padding:6px 9px}
  .brand-small{gap:7px;flex:0 1 auto;overflow:hidden}
  .brand-small .auth-mark{width:30px;height:30px}
  .brand-small .auth-mark img{width:26px;height:26px}
  .brand-small strong{font-size:11.5px;letter-spacing:.06em;white-space:nowrap}
  .brand-small small{display:none}
  .userchip{padding:3px 8px 3px 3px;gap:6px;max-width:118px}
  .userchip .avatar{width:24px;height:24px;font-size:10px}
  .userchip .uname{font-size:11px;max-width:60px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .userchip .urating{font-size:9.5px}
  .pill{padding:3px 7px;font-size:9.5px}
  .lobby{padding:12px 10px 40px;gap:12px}
  .lobby .col{gap:12px}
  .card{padding:13px;border-radius:0}
  .statgrid{gap:0}
  .stat b{font-size:16px}
  .stat span{font-size:8.5px}
  .gamewrap{padding:10px 9px 30px;gap:12px}
  .board-frame{width:100%;padding:8px}
  .board-frame::before{height:2px}
  .playerbar{padding:7px 10px;min-height:48px}
  .playerbar .who b{font-size:13.5px}
  .gameactions{grid-template-columns:repeat(2,minmax(0,1fr))}
  .playerbar{padding:6px 9px;min-height:44px}
  .playerbar .who b{max-width:38vw;font-size:12.5px}
  .captured img{width:17px;height:17px}
  .toasts{right:8px;left:8px;bottom:8px;max-width:none}
  .toast{padding:9px 11px}
  .toast span{font-size:11px}
  #gameMeta{display:none}
  .auth-tabs button{padding:10px 6px;font-size:12.5px}
  dialog{padding:18px}
  .result-banner .delta{font-size:22px}
  .ring-card{padding:18px 15px 15px}
  .ring-avatar{width:62px;height:62px;font-size:24px}
  .spectator-banner{font-size:11.5px;padding:8px 10px}
  .chat-log{max-height:150px}
  .live-row{flex-wrap:wrap;gap:7px}
  .live-row .meta{width:100%;justify-content:space-between}
}
`;

/* The artwork itself is injected once and reused by the browser renderer. */
const FRONTEND_BOOT = {
  palettes: PIECE_PALETTES,
  art: PIECE_ART,
  pedestal: PEDESTAL_ART,
  pieceNames: PIECE_NAMES,
  pieceValues: PIECE_VALUES,
};

/**
 * The single page application shell. Returned for every non-API GET request so
 * the client can handle routing after it knows whether a session exists.
 */
function renderApp() {
  const bootJson = JSON.stringify(FRONTEND_BOOT).replace(/</g, '\\u003c');
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#008080">
<title>Grandmaster — Online Chess</title>
<!-- Playfair Display (display) · Merriweather (body) · Poppins (UI) · Libre Baskerville (numerals/quotes).
     The stacks below also carry Baskerville/Georgia and system-sans fallbacks, so the app still
     renders in its intended hierarchy when the font CDN is unreachable (offline / sandboxed preview). -->
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Playfair+Display:ital,wght@0,500;0,600;0,700;1,500&family=Merriweather:ital,wght@0,300;0,400;0,700;1,400&family=Poppins:wght@400;500;600;700&family=Libre+Baskerville:ital,wght@0,400;0,700;1,400&display=swap">
<style>${APP_CSS}</style>
</head>
<body>
<div id="boot-splash" class="view splash">
  <div style="text-align:center">
    <div style="width:60px;height:60px;margin:0 auto 16px;border:1px solid var(--teal-line);display:grid;place-items:center;background:#fff" id="splashMark"></div>
    <h2 style="font-family:var(--font-display);font-weight:600;font-size:24px;letter-spacing:.2em;color:var(--teal-deep)">GRANDMASTER</h2>
    <p style="font-family:var(--font-sans);color:var(--muted-2);font-size:10.5px;letter-spacing:.24em;text-transform:uppercase;margin-top:11px;font-weight:500">Loading your club…</p>
  </div>
</div>

<!-- ======================= AUTH ======================= -->
<section id="viewAuth" class="view auth-view" hidden>
  <div class="auth-art">
    <img id="ghostPiece" class="ghost-piece" alt="" aria-hidden="true">
    <div class="auth-brand">
      <div class="auth-mark" id="authMark"></div>
      <div>
        <h1>GRANDMASTER</h1>
        <span>Online chess club</span>
      </div>
    </div>
    <h2>Play real people.<br><em>Earn every point</em> you capture.</h2>
    <p>A rated online chess club with an unusual economy: your rating rises from the material you actually capture. Invite a rival, play live, and watch the leaderboard move.</p>
    <div class="auth-features">
      <div class="auth-feature"><span class="ico">♟</span><div><b>Live multiplayer</b> — invitations, matchmaking, and reconnect-safe games.</div></div>
      <div class="auth-feature"><span class="ico">⚖</span><div><b>Capture-based rating</b> — pawn 1 · bishop 2 · knight 3 · rook 4 · queen 5.</div></div>
      <div class="auth-feature"><span class="ico">✦</span><div><b>Three AI levels</b> — a legal-move engine that never cheats.</div></div>
    </div>
  </div>
  <div class="auth-panel">
    <div class="auth-card">
      <div class="auth-tabs" role="tablist">
        <button id="tabLogin" class="active" role="tab" aria-selected="true" type="button">Sign in</button>
        <button id="tabSignup" role="tab" aria-selected="false" type="button">Create account</button>
      </div>

      <form id="loginForm" autocomplete="on" novalidate>
        <div class="field">
          <label for="loginIdentifier">Email or username</label>
          <input id="loginIdentifier" name="identifier" autocomplete="username" placeholder="you@example.com">
        </div>
        <div class="field">
          <label for="loginPassword">Password</label>
          <input id="loginPassword" name="password" type="password" autocomplete="current-password" placeholder="Your password">
        </div>
        <div class="form-msg" id="loginMsg" role="alert"></div>
        <button class="btn primary block" id="loginSubmit" type="submit">Sign in</button>
        <p class="fine-print">Every account starts at <b>500</b> rating points. Sessions live in MongoDB and are carried by an httpOnly cookie.</p>
      </form>

      <form id="signupForm" autocomplete="on" novalidate hidden>
        <div class="field">
          <label for="suUsername">Username</label>
          <input id="suUsername" name="username" autocomplete="username" placeholder="3–20 characters, letters and numbers">
        </div>
        <div class="field">
          <label for="suEmail">Email</label>
          <input id="suEmail" name="email" type="email" autocomplete="email" placeholder="you@example.com">
        </div>
        <div class="field">
          <label for="suPassword">Password</label>
          <input id="suPassword" name="password" type="password" autocomplete="new-password" placeholder="At least 8 characters, one number">
        </div>
        <div class="field">
          <label for="suConfirm">Confirm password</label>
          <input id="suConfirm" name="confirmPassword" type="password" autocomplete="new-password" placeholder="Repeat your password">
        </div>
        <div class="form-msg" id="signupMsg" role="alert"></div>
        <button class="btn primary block" id="signupSubmit" type="submit">Create account · start at 500</button>
        <p class="fine-print">Passwords are hashed with bcrypt. Declining an invitation costs <b>you</b> ${DECLINE_PENALTY} points — the player who invited you loses nothing — so accept only the games you want.</p>
      </form>
    </div>
  </div>
</section>

<!-- ======================= LOBBY ======================= -->
<section id="viewLobby" class="view" hidden>
  <header class="topbar">
    <div class="brand-small">
      <div class="auth-mark" id="lobbyMark"></div>
      <div><strong>GRANDMASTER</strong><small>Online chess club</small></div>
    </div>
    <div class="topbar-right">
      <span class="pill live" id="connPill"><span class="dot"></span>Live</span>
      <div class="userchip">
        <span class="avatar" id="chipAvatar">?</span>
        <div><span class="uname" id="chipName">—</span><span class="urating" id="chipRating">500</span></div>
      </div>
      <button class="btn ghost sm" id="btnSound" type="button">Sound: on</button>
      <button class="btn ghost sm" id="btnLogout" type="button">Sign out</button>
    </div>
  </header>

  <main class="lobby">
    <div class="col">
      <section class="card">
        <h3>Your profile <span class="hint" id="memberSince"></span></h3>
        <div class="rating-hero">
          <div class="big" id="statRating">500</div>
          <div class="lbl">Rating<br>points</div>
        </div>
        <div class="statgrid">
          <div class="stat"><b id="statWins">0</b><span>Wins</span></div>
          <div class="stat"><b id="statLosses">0</b><span>Losses</span></div>
          <div class="stat"><b id="statDraws">0</b><span>Draws</span></div>
          <div class="stat"><b id="statGames">0</b><span>Games</span></div>
        </div>
        <div class="rules-note" id="ratingRules"></div>
      </section>

      <section class="card">
        <h3>Play now</h3>
        <div class="seg" id="difficultySeg">
          <button type="button" data-diff="easy">Easy</button>
          <button type="button" data-diff="medium" class="active">Medium</button>
          <button type="button" data-diff="hard">Hard</button>
        </div>
        <select class="input" id="aiColor" aria-label="Choose your colour">
          <option value="w">Play as White</option>
          <option value="b">Play as Black</option>
          <option value="random">Random colour</option>
        </select>
        <div class="playgrid">
          <button class="btn emerald" id="btnPlayAi" type="button">Play the AI</button>
          <button class="btn primary" id="btnQuickMatch" type="button">Find opponent</button>
        </div>
        <div class="tiny muted" id="matchStatus" style="margin-top:9px;min-height:16px"></div>
        <div class="divider"></div>
        <div class="field" style="margin:0">
          <label for="inviteUsername">Challenge a player by username</label>
          <div class="row" style="gap:8px">
            <input id="inviteUsername" placeholder="Exact username" style="flex:1" autocomplete="off">
            <button class="btn sm" id="btnSendInvite" type="button">Send</button>
          </div>
        </div>
        <div class="tiny" style="color:var(--ink-2);margin-top:9px;line-height:1.55;border-left:3px solid var(--teal);background:var(--teal-soft-2);padding:8px 10px" id="inviteRuleNote">
          Invitation rule: if <b>you decline</b> a challenge sent to you, <b>your</b> rating drops by
          <b id="declineRulePoints">10</b> points (never below 0). The player who invited you loses nothing.
          Letting an invitation expire or cancelling your own never costs anything.
        </div>
      </section>

      <section class="card">
        <h3>Players online <span class="hint" id="onlineCount">0</span></h3>
        <div class="list" id="playersList"><div class="empty">Nobody else is online right now.</div></div>
      </section>
    </div>

    <div class="col">
      <section class="card">
        <h3>Invitations <span class="hint" id="inviteHint"></span></h3>
        <div id="inviteBox"><div class="empty">No invitations right now.</div></div>
      </section>

      <section class="card">
        <h3>Live matches <span class="hint" id="liveHint">spectate freely</span></h3>
        <div class="list" id="liveList"><div class="empty">No live matches right now.</div></div>
      </section>

      <section class="card">
        <h3>Active matches</h3>
        <div class="list" id="activeList"><div class="empty">No match in progress.</div></div>
      </section>

      <section class="card">
        <h3>Recent games</h3>
        <div class="list" id="historyList" style="max-height:400px"><div class="empty">No finished games yet.</div></div>
      </section>
    </div>

    <div class="col">
      <section class="card">
        <h3>Leaderboard <span class="hint">top 20</span></h3>
        <div id="leaderboard"><div class="empty">No players yet.</div></div>
      </section>

      <section class="card">
        <h3>Rating history</h3>
        <div class="list" id="ratingLog" style="max-height:300px"><div class="empty">No rating changes yet.</div></div>
      </section>

      <section class="card">
        <h3>Notifications <span class="hint"><button class="btn ghost sm" id="btnReadAll" type="button" style="padding:3px 8px;font-size:11px">Mark all read</button></span></h3>
        <div class="note-list" id="notifList"><div class="empty">Nothing yet.</div></div>
      </section>
    </div>
  </main>
</section>

<!-- ======================= GAME ======================= -->
<section id="viewGame" class="view" hidden>
  <header class="topbar">
    <div class="row" style="gap:10px;min-width:0">
      <button class="btn ghost sm" id="btnBack" type="button">← Lobby</button>
      <span class="pill gold" id="gameModePill">Rated match</span>
      <span class="clock" id="matchClock" hidden>10:00</span>
    </div>
    <div class="topbar-right">
      <span class="tiny muted" id="gameMeta"></span>
      <span class="spec-pill" id="watchPill" hidden>0 watching</span>
      <span class="pill live" id="gameConn"><span class="dot"></span>Live</span>
    </div>
  </header>

  <main class="gamewrap">
    <div class="boardcol">
      <div class="board-frame">
        <div class="board-shell">
          <div id="board" class="board" role="group" aria-label="Chessboard"></div>
        </div>
        <div class="board-foot">
          <span id="frameMeta">Live board</span>
          <span class="frame-dots" aria-hidden="true"><i></i><i></i><i></i></span>
        </div>
      </div>
      <div class="matchdeck">
        <div class="playerbar" id="topBar">
          <div class="who"><span class="dot" id="topDot"></span><div><b id="topName">Opponent</b><div class="pr" id="topRating">—</div></div></div>
          <div class="captured" id="topCaptured"></div>
        </div>
        <div class="playerbar" id="bottomBar">
          <div class="who"><span class="dot" id="bottomDot"></span><div><b id="bottomName">You</b><div class="pr" id="bottomRating">—</div></div></div>
          <div class="captured" id="bottomCaptured"></div>
        </div>
        <div class="spectator-banner" id="spectatorBanner" hidden>
          <span class="spec-pill" id="spectatorPill"><span class="dot"></span>spectating</span>
          <span id="spectatorText">You are watching this match. The board is read-only — nothing you send can change the position.</span>
        </div>
        <div class="status" id="status" role="status" aria-live="polite">Connecting…</div>
        <div class="gameactions" id="playerActions">
          <button class="btn ghost" id="btnFlip" type="button">Flip board</button>
          <button class="btn" id="btnDraw" type="button">Offer draw</button>
          <button class="btn" id="btnCoachToggle" type="button">Coach</button>
          <button class="btn ghost" id="btnLeave" type="button">Leave match</button>
          <button class="btn danger" id="btnResign" type="button">Resign</button>
        </div>
        <div class="gameactions" id="spectatorActions" hidden>
          <button class="btn ghost" id="btnFlipSpec" type="button">Flip board</button>
          <button class="btn ghost" id="btnLeaveSpec" type="button">Stop watching</button>
        </div>
      </div>
    </div>

    <aside class="sidepanel">
      <div class="scorebox">
        <div class="scorecard"><span id="scoreYouLabel">Your captures</span><b id="scoreYou">0</b><span class="tiny" id="scoreYouDetail" style="text-transform:none;letter-spacing:0;color:var(--muted-2)">0 pieces captured</span></div>
        <div class="scorecard"><span id="scoreOppLabel">Their captures</span><b id="scoreOpp">0</b><span class="tiny" id="scoreOppDetail" style="text-transform:none;letter-spacing:0;color:var(--muted-2)">0 pieces captured</span></div>
      </div>
      <div id="resultSlot"></div>
      <div class="offer-banner" id="drawOfferBanner" hidden>
        <div id="drawOfferText" class="tiny">Your opponent offers a draw.</div>
        <div class="row2">
          <button class="btn sm emerald" id="btnAcceptDraw" type="button">Accept draw</button>
          <button class="btn sm ghost" id="btnDeclineDraw" type="button">Decline</button>
        </div>
      </div>
      <section class="card" style="padding:13px 14px">
        <h3 style="margin-bottom:8px">Moves <span class="hint" id="moveCount">0 plies</span></h3>
        <div class="movelist" id="moveList"><div class="empty">The game has not started.</div></div>
      </section>
      <section class="card" id="chatPanel">
        <h3 style="margin-bottom:8px">Match chat <span class="hint" id="chatHint">suggestions only</span></h3>
        <div class="chat-log" id="chatLog"><div class="chat-msg system">Say hello, suggest a move, or comment on this game. Chat never changes the board.</div></div>
        <form class="chat-form" id="chatForm" autocomplete="off">
          <input class="input" id="chatInput" maxlength="240" placeholder="Suggest a move…" aria-label="Match chat message">
          <button class="btn sm emerald" type="submit">Send</button>
        </form>
      </section>
      <section class="card coach-box" id="coachPanel" hidden>
        <h3 style="margin-bottom:4px">Chess coach <span class="hint">optional</span></h3>
        <div class="coach-log" id="coachLog"><div class="coach-msg">Ask about the current position. Answers come from the server; no keys ever reach your browser.</div></div>
        <form class="coach-form" id="coachForm">
          <input id="coachInput" placeholder="What is the plan here?" maxlength="400" autocomplete="off">
          <button class="btn sm emerald" type="submit" id="coachSend">Ask</button>
        </form>
      </section>
    </aside>
  </main>
</section>

<div class="ringpop" id="ringPop" role="dialog" aria-modal="true" aria-labelledby="ringTitle" hidden>
  <div class="ring-card">
    <h4 id="ringTitle">Incoming challenge</h4>
    <div class="ring-avatar" id="ringAvatar">?</div>
    <div class="ring-name" id="ringName">—</div>
    <div class="ring-rating" id="ringRating">rating 500</div>
    <p class="ring-note" id="ringNote">
      Accept to start a rated 10-minute match right away. Declining costs <b>you</b> 10 points — the
      challenger loses nothing.
    </p>
    <div class="ring-actions">
      <button class="btn emerald" id="ringAccept" type="button">Accept</button>
      <button class="btn ring-decline" id="ringDecline" type="button">Decline</button>
    </div>
    <div class="ring-count" id="ringCount">Expires in 02:00</div>
  </div>
</div>

<div class="toasts" id="toasts" aria-live="polite"></div>

<dialog id="confirmDialog">
  <h2 id="confirmTitle">Are you sure?</h2>
  <p id="confirmBody"></p>
  <div class="dialog-actions">
    <button class="btn ghost" id="confirmCancel" type="button">Cancel</button>
    <button class="btn danger" id="confirmOk" type="button">Confirm</button>
  </div>
</dialog>

<dialog id="promotionDialog">
  <h2>Promote your pawn</h2>
  <p>Choose the piece your pawn becomes.</p>
  <div class="promo" id="promoChoices"></div>
  <div class="dialog-actions"><button class="btn ghost" id="promoCancel" type="button">Cancel</button></div>
</dialog>

<dialog id="resultDialog">
  <h2 id="resultTitle">Game over</h2>
  <div id="resultBody"></div>
  <div class="dialog-actions">
    <button class="btn ghost" id="resultLobby" type="button">Back to lobby</button>
    <button class="btn primary" id="resultRematch" type="button">Play again</button>
  </div>
</dialog>

<script src="/socket.io/socket.io.js"></script>
<script>window.__BOOT__ = ${bootJson};</script>
<script>
(function () {
  'use strict';
  var BOOT = window.__BOOT__ || {};
  var S = {
    user: null, config: null, lobby: null, game: null,
    selected: null, flipped: false, flipManual: false,
    socket: null, awaiting: false, diff: 'medium', sound: true,
    promo: null, matchmaking: false, lobbyTimer: null,
    resultShown: null, coachOpen: false,
    spectating: false, spectatorCount: 0, chatSeen: {},
    ring: null, ringing: null, clockDeadline: 0, clockTimer: null,
    reauthTried: false, verifying: false
  };

  /* ----------------------------------------------------------- session token
   * The server also returns a bearer token at sign-in. Keeping it in
   * localStorage means a sign-in still works when the browser refuses or drops
   * the session cookie (plain-HTTP production, blocked third-party cookies,
   * "block all cookies" settings), which used to bounce new players straight
   * back to the sign-in screen. */
  var TOKEN_KEY = 'grandmaster.token';
  var memoryToken = '';
  function getToken() {
    if (memoryToken) return memoryToken;
    try {
      memoryToken = window.localStorage.getItem(TOKEN_KEY) || '';
    } catch (err) { memoryToken = ''; }
    return memoryToken;
  }
  function setToken(value) {
    memoryToken = typeof value === 'string' ? value : '';
    try {
      if (memoryToken) window.localStorage.setItem(TOKEN_KEY, memoryToken);
      else window.localStorage.removeItem(TOKEN_KEY);
    } catch (err) { /* storage may be blocked — the in-memory copy still works */ }
  }
  function clearToken() { setToken(''); }

  /* ------------------------------------------------------------------ utils */
  function $(id) { return document.getElementById(id); }
  function esc(value) {
    return String(value == null ? '' : value)
      .split('&').join('&amp;')
      .split('<').join('&lt;')
      .split('>').join('&gt;')
      .split('"').join('&quot;')
      .split("'").join('&#39;');
  }
  function fmtAgo(value) {
    if (!value) return '';
    var diff = Math.max(0, Date.now() - new Date(value).getTime());
    var mins = Math.round(diff / 60000);
    if (mins < 1) return 'just now';
    if (mins < 60) return mins + 'm ago';
    var hours = Math.round(mins / 60);
    if (hours < 24) return hours + 'h ago';
    return Math.round(hours / 24) + 'd ago';
  }
  function fmtClock(ms) {
    var total = Math.max(0, Math.round(ms / 1000));
    var m = Math.floor(total / 60);
    var s = total % 60;
    return m + ':' + (s < 10 ? '0' : '') + s;
  }
  function prettyReason(reason) {
    return String(reason || '').split('-').join(' ');
  }
  function toast(title, body, kind) {
    var box = $('toasts');
    if (!box) return;
    /* Never let notifications pile up over the board. */
    while (box.children.length >= 2) box.removeChild(box.firstChild);
    var el = document.createElement('div');
    el.className = 'toast ' + (kind || '');
    el.innerHTML = '<b>' + esc(title) + '</b>' + (body ? '<span>' + esc(body) + '</span>' : '');
    box.appendChild(el);
    setTimeout(function () {
      el.style.opacity = '0';
      el.style.transform = 'translateY(8px)';
      el.style.transition = 'opacity .25s, transform .25s';
      setTimeout(function () { if (el.parentNode) el.parentNode.removeChild(el); }, 260);
    }, 4200);
  }
  function api(path, options) {
    var opts = options || {};
    var init = { method: opts.method || 'GET', credentials: 'same-origin', headers: { 'Content-Type': 'application/json' } };
    var token = getToken();
    if (token) init.headers['x-gm-token'] = token;
    if (opts.body) init.body = JSON.stringify(opts.body);
    return fetch('/api' + path, init).then(function (res) {
      return res.json().catch(function () { return {}; }).then(function (data) {
        if (!res.ok) {
          var err = new Error((data && data.error) || 'Request failed');
          err.code = data && data.code;
          err.status = res.status;
          throw err;
        }
        return data;
      });
    });
  }

  /* -------------------------------------------------------------- chess art */
  var PIECE_URLS = {};
  function buildPieceSvg(color, type) {
    var pal = BOOT.palettes && BOOT.palettes[color];
    var art = BOOT.art && BOOT.art[type];
    if (!pal || !art) return '';
    function grad(id, stops) {
      return '<linearGradient id="' + id + '" x1="0" y1="0" x2="1" y2="1">' +
        '<stop stop-color="' + stops[0] + '"/><stop offset=".52" stop-color="' + stops[1] + '"/>' +
        '<stop offset="1" stop-color="' + stops[2] + '"/></linearGradient>';
    }
    var style = '.edge{stroke:' + pal.edge + ';stroke-width:9;stroke-linejoin:round;stroke-linecap:round} ' +
      '.fine{fill:none;stroke-width:5;stroke-linecap:round;stroke-linejoin:round} ' +
      '.body{fill:url(#gm-body)} .light{fill:url(#gm-light)} .metal{fill:url(#gm-metal)} .skin{fill:url(#gm-skin)} ' +
      '.dark{fill:' + pal.dark + '} .shadow{fill:' + pal.shadow + ';opacity:.17} .crease{stroke:' + pal.crease + '} ' +
      '.goldline{stroke:' + pal.goldline + '} .ink{stroke:' + pal.ink + '} .shine{stroke:' + pal.shine + ';fill:' + pal.shine + '}';
    return '<svg xmlns="http://www.w3.org/2000/svg" width="1000" height="1000" viewBox="0 0 1000 1000" role="img">' +
      '<defs>' + grad('gm-body', pal.body) + grad('gm-light', pal.light) + grad('gm-metal', pal.metal) + grad('gm-skin', pal.skin) +
      '<style>' + style + '</style></defs>' +
      '<g transform="' + art.transform + '"><g id="' + art.id + '">' + art.art + '</g></g>' +
      '<g id="pedestal">' + BOOT.pedestal + '</g></svg>';
  }
  function pieceUrl(color, type) {
    var key = color + type;
    if (!PIECE_URLS[key]) {
      PIECE_URLS[key] = 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent(buildPieceSvg(color, type));
    }
    return PIECE_URLS[key];
  }
  function pieceImg(color, type) {
    var img = document.createElement('img');
    img.className = 'piece';
    img.alt = '';
    img.draggable = false;
    img.src = pieceUrl(color, type);
    return img;
  }
  function inlinePiece(color, type, size) {
    return '<img src="' + pieceUrl(color, type) + '" alt="" style="width:' + size + 'px;height:' + size + 'px;display:block">';
  }
  function parseFen(fen) {
    var board = {};
    var ranks = String(fen || '').split(' ')[0].split('/');
    for (var r = 0; r < 8; r += 1) {
      var row = ranks[r] || '';
      var file = 0;
      for (var i = 0; i < row.length; i += 1) {
        var ch = row.charAt(i);
        if (ch >= '1' && ch <= '8') {
          file += Number(ch);
        } else {
          board[String.fromCharCode(97 + file) + (8 - r)] = {
            color: ch === ch.toUpperCase() ? 'w' : 'b',
            type: ch.toLowerCase()
          };
          file += 1;
        }
      }
    }
    return board;
  }

  /* ------------------------------------------------------------------ sound */
  var audioCtx = null;
  function playCue(kind) {
    if (!S.sound) return;
    try {
      var Ctx = window.AudioContext || window.webkitAudioContext;
      if (!Ctx) return;
      audioCtx = audioCtx || new Ctx();
      if (audioCtx.state === 'suspended') audioCtx.resume();
      var osc = audioCtx.createOscillator();
      var gain = audioCtx.createGain();
      var now = audioCtx.currentTime;
      osc.type = kind === 'capture' ? 'square' : kind === 'end' ? 'triangle' : 'sine';
      osc.frequency.setValueAtTime(kind === 'capture' ? 300 : kind === 'end' ? 220 : kind === 'ring' ? 660 : 420, now);
      osc.frequency.exponentialRampToValueAtTime(kind === 'end' ? 120 : 170, now + 0.12);
      gain.gain.setValueAtTime(0.05, now);
      gain.gain.exponentialRampToValueAtTime(0.0008, now + 0.16);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start(now);
      osc.stop(now + 0.17);
    } catch (err) { /* audio is decorative only */ }
  }

  /* A challenge rings like an incoming call until it is answered. */
  function startRinging() {
    stopRinging();
    if (!S.sound) return;
    playCue('ring');
    S.ringing = setInterval(function () { playCue('ring'); }, 1900);
  }
  function stopRinging() {
    if (S.ringing) { clearInterval(S.ringing); S.ringing = null; }
  }

  /* ----------------------------------------------------------------- socket */
  function socketEmit(event, payload, cb) {
    var s = S.socket;
    if (!s || !s.connected) {
      if (cb) cb({ ok: false, error: 'Connection lost. Reconnecting…' });
      return;
    }
    var settled = false;
    var timer = setTimeout(function () {
      if (settled) return;
      settled = true;
      if (cb) cb({ ok: false, error: 'The server did not respond. Please try again.' });
    }, 9000);
    s.emit(event, payload, function (res) {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (cb) cb(res || { ok: false, error: 'No response from the server.' });
    });
  }

  function setConn(online) {
    ['connPill', 'gameConn'].forEach(function (id) {
      var el = $(id);
      if (!el) return;
      el.className = 'pill ' + (online ? 'live' : 'off');
      el.innerHTML = '<span class="dot' + (online ? '' : ' off') + '"></span>' + (online ? 'Live' : 'Offline');
    });
  }

  function scheduleLobbyRefresh() {
    if (S.lobbyTimer) return;
    S.lobbyTimer = setTimeout(function () {
      S.lobbyTimer = null;
      if ($('viewLobby') && !$('viewLobby').hidden) loadLobby();
    }, 500);
  }

  function connectSocket() {
    if (S.socket || typeof window.io !== 'function') return;
    var socket = window.io({ withCredentials: true, auth: { token: getToken() }, reconnectionDelay: 800, reconnectionDelayMax: 5000 });
    S.socket = socket;

    socket.on('connect', function () {
      setConn(true);
      if (S.game) socketEmit('game:join', { gameId: S.game.gameId }, function () {});
      if (S.matchmaking) socketEmit('matchmaking:join', {}, function () {});
    });
    socket.on('disconnect', function () {
      setConn(false);
      toast('Connection lost', 'Trying to reconnect…', 'error');
    });
    socket.on('connect_error', function (err) {
      setConn(false);
      /* A stale token is worth replacing before the user sees anything: ask the
       * server who we are, then retry the handshake once. */
      if (err && /unauthenticated/i.test(err.message || '') && !S.reauthTried) {
        S.reauthTried = true;
        api('/auth/me')
          .then(function (res) {
            S.user = res.user;
            S.config = res.config || S.config;
            socket.auth = { token: getToken() };
            socket.connect();
          })
          .catch(function () { S.reauthTried = false; });
      }
    });

    socket.on('presence:list', function (payload) {
      if (!S.lobby || !payload) return;
      var mine = S.user && S.user.username;
      S.lobby.online = (payload.online || []).filter(function (p) { return p.username !== mine; });
      renderPlayers();
    });

    socket.on('presence:update', function (p) {
      if (!S.lobby || !p || !S.user || p.username === S.user.username) return;
      var list = S.lobby.online || [];
      var found = false;
      for (var i = 0; i < list.length; i += 1) {
        if (list[i].id === p.userId) {
          found = true;
          if (!p.online) { list.splice(i, 1); }
          else { list[i].rating = p.rating; list[i].username = p.username; }
          break;
        }
      }
      if (!found && p.online) list.push({ id: p.userId, username: p.username, rating: p.rating, inGame: false });
      S.lobby.online = list;
      renderPlayers();
    });

    socket.on('notification', function (n) {
      if (!n) return;
      /* game:start / game:ended already surface their own toast for the same
       * event, so skip the duplicate notification pop-up. */
      var alreadyAnnounced = n.type === 'invitation-accepted' || n.type === 'game-result' ||
        n.type === 'invitation-rejected' || n.type === 'invitation' || n.type === 'live-match';
      if (!alreadyAnnounced) toast(n.title || 'Notification', n.body || '', 'info');
      scheduleLobbyRefresh();
    });

    socket.on('info', function (payload) {
      if (payload && payload.message) toast('Heads up', payload.message, 'info');
    });

    socket.on('invitation:new', function (inv) {
      if (!inv) return;
      showChallengeRing(inv);
      toast('Incoming challenge', inv.username + ' (' + inv.rating + ') wants a rated match.', 'info');
      scheduleLobbyRefresh();
    });

    socket.on('invitation:update', function (inv) {
      if (!inv) return;
      if (inv.status === 'rejected' || inv.status === 'declined') {
        var penalty = typeof inv.penalty === 'number' ? inv.penalty : 0;
        if (penalty > 0 && inv.username && S.user && inv.username === S.user.username) {
          toast('You declined', 'You lost ' + penalty + ' point' + (penalty === 1 ? '' : 's') + '.', 'error');
        } else {
          toast('Invitation declined', inv.username + ' declined your challenge. No points were deducted from you.', 'info');
        }
      } else if (inv.status === 'expired') {
        toast('Invitation expired', 'No penalty was applied.', 'info');
      } else if (inv.status === 'accepted') {
        toast('Invitation accepted', 'Preparing the board…', 'success');
      } else if (inv.status === 'cancelled') {
        toast('Invitation unavailable', 'The challenge was cancelled.', 'info');
      }
      if (S.ring && S.ring.id === inv.id && inv.status !== 'pending') hideChallengeRing();
      scheduleLobbyRefresh();
    });

    socket.on('game:start', function (payload) {
      if (!payload || !payload.gameId) return;
      if (S.ring) hideChallengeRing();
      toast('Match ready', 'You play ' + (payload.you === 'w' ? 'White' : 'Black') + ' against ' + payload.opponentName + '.', 'success');
      scheduleLobbyRefresh();
      openGame(payload.gameId);
    });

    socket.on('matchmaking:waiting', function (payload) {
      S.matchmaking = true;
      $('btnQuickMatch').textContent = 'Cancel search';
      $('matchStatus').textContent = 'Searching for an opponent… queue position ' + ((payload && payload.queuePosition) || 1);
    });
    socket.on('matchmaking:matched', function (payload) {
      S.matchmaking = false;
      $('btnQuickMatch').textContent = 'Find opponent';
      $('matchStatus').textContent = 'Opponent found.';
      if (payload && payload.gameId) openGame(payload.gameId);
    });
    socket.on('matchmaking:cancelled', function (payload) {
      S.matchmaking = false;
      $('btnQuickMatch').textContent = 'Find opponent';
      $('matchStatus').textContent = '';
      toast('Matchmaking stopped', (payload && payload.reason) || 'Please try again.', 'error');
      scheduleLobbyRefresh();
    });

    socket.on('game:state', function (state) {
      if (!state || !state.gameId) return;
      if (S.game && S.game.gameId !== state.gameId) {
        scheduleLobbyRefresh();
        return;
      }
      applyGameState(state);
      scheduleLobbyRefresh();
    });

    socket.on('game:chat', function (msg) {
      if (!msg || !msg.gameId) return;
      appendChat(msg);
    });

    socket.on('spectate:count', function (payload) {
      if (!payload || !S.game || payload.gameId !== S.game.gameId) return;
      S.spectatorCount = payload.count || 0;
      S.game.spectators = S.spectatorCount;
      renderSpectatorMeta();
      renderWatchPill();
    });

    socket.on('live:match:start', function (payload) {
      if (!payload || !S.lobby) { scheduleLobbyRefresh(); return; }
      var mine = S.game && S.game.gameId === payload.gameId;
      if (!mine && S.user && payload.white !== S.user.username && payload.black !== S.user.username) {
        toast('Live match started', payload.white + ' is playing ' + payload.black + '. You can watch it from the lobby.', 'info');
      }
      scheduleLobbyRefresh();
    });

    socket.on('live:match:end', function () {
      scheduleLobbyRefresh();
    });

    socket.on('game:ended', function (state) {
      if (!state || !state.gameId) return;
      applyGameState(state);
      playCue('end');
      showResult(state, state.ratingDelta || 0, state.summary || '');
      scheduleLobbyRefresh();
    });
  }

  /* ------------------------------------------------------------- auth flow */
  function showView(name) {
    ['viewAuth', 'viewLobby', 'viewGame'].forEach(function (id) {
      var el = $(id);
      if (el) el.hidden = id !== name;
    });
    var splash = $('boot-splash');
    if (splash) splash.hidden = true;
  }

  function setFormMsg(el, text, ok) {
    if (!el) return;
    el.textContent = text || '';
    el.className = 'form-msg' + (ok ? ' ok' : '');
  }

  function switchAuthTab(which) {
    var login = which === 'login';
    $('tabLogin').classList.toggle('active', login);
    $('tabSignup').classList.toggle('active', !login);
    $('tabLogin').setAttribute('aria-selected', login ? 'true' : 'false');
    $('tabSignup').setAttribute('aria-selected', login ? 'false' : 'true');
    $('loginForm').hidden = !login;
    $('signupForm').hidden = login;
  }

  function doSignup(event) {
    event.preventDefault();
    var msg = $('signupMsg');
    var payload = {
      username: $('suUsername').value.trim(),
      email: $('suEmail').value.trim(),
      password: $('suPassword').value,
      confirmPassword: $('suConfirm').value
    };
    if (!payload.username || !payload.email || !payload.password) {
      setFormMsg(msg, 'Please fill in every field.');
      return;
    }
    if (payload.password !== payload.confirmPassword) {
      setFormMsg(msg, 'Passwords do not match.');
      return;
    }
    var btn = $('signupSubmit');
    btn.disabled = true;
    setFormMsg(msg, 'Creating your account…', true);
    api('/auth/signup', { method: 'POST', body: payload })
      .then(function (res) {
        if (res.token) setToken(res.token);
        S.user = res.user;
        S.config = res.config;
        setFormMsg(msg, 'Account created. Opening your club…', true);
        return verifySession(2).then(function (ok) {
          if (!ok) {
            /* Keep the credentials out of the way and tell the user exactly what
             * happened instead of looping them back to an empty form. */
            setFormMsg(msg, SESSION_LOST_TEXT);
            switchAuthTab('login');
            $('loginIdentifier').value = payload.username;
            return;
          }
          S.reauthTried = false;
          enterApp(null);
        });
      })
      .catch(function (err) { setFormMsg(msg, err.message); })
      .then(function () { btn.disabled = false; });
  }

  function doLogin(event) {
    event.preventDefault();
    var msg = $('loginMsg');
    var payload = { identifier: $('loginIdentifier').value.trim(), password: $('loginPassword').value };
    if (!payload.identifier || !payload.password) {
      setFormMsg(msg, 'Enter your email or username and password.');
      return;
    }
    var btn = $('loginSubmit');
    btn.disabled = true;
    setFormMsg(msg, 'Signing in…', true);
    api('/auth/login', { method: 'POST', body: payload })
      .then(function (res) {
        if (res.token) setToken(res.token);
        S.user = res.user;
        S.config = res.config;
        return verifySession(2).then(function (ok) {
          if (!ok) {
            setFormMsg(msg, SESSION_LOST_TEXT);
            return;
          }
          S.reauthTried = false;
          enterApp(res.activeGameId || null);
        });
      })
      .catch(function (err) { setFormMsg(msg, err.message); })
      .then(function () { btn.disabled = false; });
  }

  function doLogout() {
    api('/auth/logout', { method: 'POST' })
      .catch(function () { return null; })
      .then(function () {
        setPath('/');
        if (S.socket) {
          if (S.spectating && S.game) S.socket.emit('spectate:leave', { gameId: S.game.gameId });
          S.socket.close();
          S.socket = null;
        }
        hideChallengeRing();
        clearToken();
        S.user = null; S.lobby = null; S.game = null;
        S.spectating = false;
        S.clockDeadline = 0;
        $('matchClock').hidden = true;
        showView('viewAuth');
        switchAuthTab('login');
        $('loginPassword').value = '';
        setFormMsg($('loginMsg'), 'You have been signed out.', true);
      });
  }

  /**
   * Confirm the server really recognises this browser before showing the lobby.
   * A session can be lost even though the sign-up call succeeded (cookie
   * refused, storage cleared, proxy stripping headers), and silently dropping
   * the player back on the form is exactly the bug this guards against.
   */
  function verifySession(attempts) {
    var left = attempts == null ? 2 : attempts;
    return api('/auth/me')
      .then(function (res) {
        if (res && res.user) { S.user = res.user; S.config = res.config || S.config; return true; }
        return false;
      })
      .catch(function (err) {
        if (left > 0 && (!err.status || err.status >= 500)) {
          return new Promise(function (resolve) { setTimeout(resolve, 350); }).then(function () {
            return verifySession(left - 1);
          });
        }
        if (left > 0 && err.status === 401) {
          /* One immediate retry covers a cookie that is still landing. */
          return new Promise(function (resolve) { setTimeout(resolve, 250); }).then(function () {
            return verifySession(left - 1);
          });
        }
        return false;
      });
  }

  var SESSION_LOST_TEXT =
    'You are signed in, but this browser did not keep your session. ' +
    'Enable cookies (or leave private browsing) and try again — your account already exists.';

  /* Keep the address bar in sync with the view so a refresh lands on the right
   * screen. Always a relative path — never a hardcoded host. */
  function setPath(path) {
    try {
      if (window.location.pathname !== path) window.history.replaceState({ section: path }, '', path);
    } catch (err) { /* history is optional */ }
  }

  /* ------------------------------------------------------------ lobby views */
  function enterApp(activeGameId) {
    showView('viewLobby');
    setPath('/lobby');
    connectSocket();
    renderUserChip();
    loadLobby().then(function () {
      if (activeGameId) openGame(activeGameId);
    });
  }

  function renderUserChip() {
    if (!S.user) return;
    $('chipName').textContent = S.user.username;
    $('chipRating').textContent = S.user.rating + ' rating';
    $('chipAvatar').textContent = S.user.username.slice(0, 1).toUpperCase();
    $('statRating').textContent = S.user.rating;
    $('statWins').textContent = S.user.wins;
    $('statLosses').textContent = S.user.losses;
    $('statDraws').textContent = S.user.draws;
    $('statGames').textContent = S.user.gamesPlayed;
    if (S.user.createdAt) {
      var joined = new Date(S.user.createdAt);
      if (!isNaN(joined.getTime())) {
        $('memberSince').textContent = 'Member since ' + joined.toLocaleDateString(undefined, { month: 'short', year: 'numeric' });
      }
    }
  }

  function loadLobby() {
    return api('/lobby')
      .then(function (data) {
        S.lobby = data;
        S.user = data.user;
        S.config = data.config || S.config;
        renderUserChip();
        renderRules();
        renderPlayers();
        renderInvites();
        renderLive();
        renderActiveGames();
        renderHistory();
        renderLeaderboard();
        renderRatingLog();
        renderNotifications();
        return data;
      })
      .catch(function (err) {
        if (err.status !== 401) {
          toast('Could not refresh the lobby', err.message, 'error');
          return;
        }
        /* Do not silently throw the player back to the form — check once more,
         * then explain what happened. */
        return verifySession(1).then(function (ok) {
          if (ok) return loadLobby();
          S.user = null;
          clearToken();
          showView('viewAuth');
          switchAuthTab('login');
          setFormMsg($('loginMsg'), SESSION_LOST_TEXT);
          return null;
        });
      });
  }

  function renderRules() {
    var cfg = S.config || {};
    var values = cfg.pieceValues || { p: 1, b: 2, n: 3, r: 4, q: 5 };
    var decline = typeof cfg.declinePenalty === 'number' ? cfg.declinePenalty : 10;
    var forfeit = typeof cfg.forfeitPenalty === 'number' ? cfg.forfeitPenalty : 10;
    var minutes = Math.round((cfg.pvpMatchSeconds || 600) / 60);
    $('ratingRules').innerHTML =
      '<b>Capture economy.</b> Pawn ' + values.p + ' · Bishop ' + values.b + ' · Knight ' + values.n +
      ' · Rook ' + values.r + ' · Queen ' + values.q + ' · King 0.<br>' +
      'A win transfers exactly the points you captured; the same amount is deducted from your opponent. ' +
      'Draws transfer nothing.<br>' +
      '<b>Invitations.</b> Declining an invitation costs <b>you</b> ' + decline + ' points; the inviter pays nothing. ' +
      'Expired or cancelled invitations are free.<br>' +
      '<b>Matches.</b> Every live game lasts ' + minutes + ' minutes — if nobody is mated, the player with more ' +
      'captured material wins. Walking out of a live match costs ' + forfeit + ' points; leaving a practice game is free. ' +
      ((cfg.aiRated) ? 'AI games are rated here.' : 'AI practice games never change ratings.');
    var rulePoints = $('declineRulePoints');
    if (rulePoints) rulePoints.textContent = String(decline);
  }

  function renderPlayers() {
    if (!S.lobby) return;
    var box = $('playersList');
    var online = (S.lobby.online || []).slice().sort(function (a, b) { return b.rating - a.rating; });
    $('onlineCount').textContent = online.length + ' online';
    if (!online.length) {
      box.innerHTML = '<div class="empty">Nobody else is online right now. You can still invite someone by username.</div>';
      return;
    }
    box.innerHTML = online.map(function (p) {
      var status = p.inGame ? 'in a match' : 'available';
      return '<div class="list-row">' +
        '<div class="who"><b>' + esc(p.username) + '</b>' +
        '<span><span class="dot ' + (p.inGame ? 'busy' : '') + '" style="display:inline-block;margin-right:5px"></span>' +
        status + '</span></div>' +
        '<div class="row" style="gap:8px"><span class="rating-tag">' + p.rating + '</span>' +
        '<button class="btn sm" data-invite="' + esc(p.username) + '"' + (p.inGame ? ' disabled' : '') +
        ' type="button">Invite</button></div></div>';
    }).join('');
  }

  function declinePoints() {
    return (S.config && typeof S.config.declinePenalty === 'number') ? S.config.declinePenalty : 10;
  }

  function forfeitPoints() {
    return (S.config && typeof S.config.forfeitPenalty === 'number') ? S.config.forfeitPenalty : 10;
  }

  function renderInvites() {
    if (!S.lobby) return;
    var box = $('inviteBox');
    var incoming = S.lobby.invitations.incoming || [];
    var outgoing = S.lobby.invitations.outgoing || [];
    $('inviteHint').textContent = incoming.length + ' in · ' + outgoing.length + ' out';
    if (!incoming.length && !outgoing.length) {
      box.innerHTML = '<div class="empty">No invitations right now.</div>';
      return;
    }
    var html = '';
    incoming.forEach(function (inv) {
      html += '<div class="invite-row">' +
        '<div class="who"><b>' + esc(inv.username) + '</b>' +
        '<span class="tiny muted">rating ' + inv.rating + ' · <span class="countdown" data-since="' + inv.expiresAt + '">' +
        fmtClock(new Date(inv.expiresAt) - Date.now()) + '</span> left · declining costs you ' + declinePoints() + '</span></div>' +
        '<button class="btn sm emerald" data-accept="' + esc(inv.id) + '" type="button">Accept</button>' +
        '<button class="btn sm ghost" data-reject="' + esc(inv.id) + '" data-name="' + esc(inv.username) + '" type="button">Decline</button>' +
        '</div>';
    });
    outgoing.forEach(function (inv) {
      html += '<div class="invite-row" style="border-color:var(--line);background:var(--surface-2)">' +
        '<div class="who"><b>To ' + esc(inv.username) + '</b>' +
        '<span class="tiny muted">waiting · <span class="countdown" data-since="' + inv.expiresAt + '">' +
        fmtClock(new Date(inv.expiresAt) - Date.now()) + '</span> left · they pay the price if they decline</span></div>' +
        '<button class="btn sm ghost" data-cancel="' + esc(inv.id) + '" type="button">Cancel</button>' +
        '</div>';
    });
    box.innerHTML = html;
  }

  function renderLive() {
    if (!S.lobby) return;
    var box = $('liveList');
    var games = (S.lobby.liveMatches || []);
    $('liveHint').textContent = games.length ? (games.length + ' live · spectate freely') : 'nothing live';
    if (!games.length) {
      box.innerHTML = '<div class="empty">No live matches right now. Start one and the whole club is notified.</div>';
      return;
    }
    box.innerHTML = games.map(function (g) {
      var left = g.clockEndsAt ? Math.max(0, new Date(g.clockEndsAt).getTime() - Date.now()) : 0;
      var tag = g.isMine ? 'your game' : 'live';
      return '<div class="live-row">' +
        '<div class="vs"><b>' + esc(g.white) + ' <span style="color:var(--teal-strong)">vs</span> ' + esc(g.black) + '</b>' +
        '<span>' + g.moves + ' plies · captured ' + (g.capturePoints.w + g.capturePoints.b) +
        ' · ' + fmtClock(left) + ' left · ' + tag + '</span></div>' +
        '<div class="meta">' +
        '<span class="spec-pill">' + (g.spectators || 0) + ' watching</span>' +
        (g.isMine
          ? '<button class="btn sm primary" data-resume="' + esc(g.gameId) + '" type="button">Open board</button>'
          : '<button class="btn sm emerald" data-spectate="' + esc(g.gameId) + '" type="button">Watch</button>') +
        '</div></div>';
    }).join('');
  }

  function renderActiveGames() {
    if (!S.lobby) return;
    var box = $('activeList');
    var games = S.lobby.activeGames || [];
    if (!games.length) {
      box.innerHTML = '<div class="empty">No match in progress.</div>';
      return;
    }
    box.innerHTML = games.map(function (g) {
      var yourTurn = g.turn === g.you;
      return '<div class="list-row">' +
        '<div class="who"><b>' + esc(g.opponentName) + '</b>' +
        '<span>' + (g.mode === 'ai' ? 'Practice · ' + esc(g.aiDifficulty || 'ai') : 'Rated') +
        ' · move ' + (Math.floor(g.ply / 2) + 1) + ' · ' + (yourTurn ? 'your turn' : 'their turn') + '</span></div>' +
        '<button class="btn sm ' + (yourTurn ? 'primary' : '') + '" data-resume="' + esc(g.gameId) + '" type="button">Resume</button>' +
        '</div>';
    }).join('');
  }

  function renderHistory() {
    if (!S.lobby) return;
    var box = $('historyList');
    var games = S.lobby.recentGames || [];
    if (!games.length) {
      box.innerHTML = '<div class="empty">No finished games yet.</div>';
      return;
    }
    box.innerHTML = games.map(function (g) {
      var outcome = g.result === 'draw' ? 'draw' : g.result === g.you ? 'win' : 'loss';
      var label = outcome === 'win' ? 'Win' : outcome === 'loss' ? 'Loss' : 'Draw';
      var deltaCls = g.ratingDelta > 0 ? 'delta-pos' : g.ratingDelta < 0 ? 'delta-neg' : 'delta-zero';
      var deltaText = (g.ratingDelta > 0 ? '+' : '') + (g.ratingDelta || 0);
      return '<div class="hist-row">' +
        '<div style="min-width:0"><b style="display:block;font-size:12.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">' +
        esc(g.opponentName) + '</b><span class="tiny muted">' + esc(prettyReason(g.resultReason)) + ' · ' + fmtAgo(g.endedAt) +
        ' · captured ' + g.capturePoints + '</span></div>' +
        '<div class="row" style="gap:8px"><span class="pill ' + outcome + '">' + label + '</span>' +
        '<span class="' + deltaCls + '">' + deltaText + '</span></div></div>';
    }).join('');
  }

  function renderLeaderboard() {
    if (!S.lobby) return;
    var board = S.lobby.leaderboard || [];
    var box = $('leaderboard');
    if (!board.length) {
      box.innerHTML = '<div class="empty">No players yet.</div>';
      return;
    }
    box.innerHTML = board.map(function (row) {
      return '<div class="lb-row' + (row.isMe ? ' me' : '') + '">' +
        '<span class="rank">' + row.rank + '</span>' +
        '<span class="nm">' + esc(row.username) + (row.isMe ? ' <span class="tiny" style="color:var(--teal-strong)">(you)</span>' : '') +
        '<span class="tiny muted"> ' + row.wins + 'W · ' + row.losses + 'L · ' + row.draws + 'D</span></span>' +
        '<span class="rating-tag">' + row.rating + '</span></div>';
    }).join('');
  }

  function renderRatingLog() {
    if (!S.lobby) return;
    var rows = S.lobby.ratingHistory || [];
    var box = $('ratingLog');
    if (!rows.length) {
      box.innerHTML = '<div class="empty">No rating changes yet.</div>';
      return;
    }
    box.innerHTML = rows.map(function (r) {
      var cls = r.change > 0 ? 'delta-pos' : r.change < 0 ? 'delta-neg' : 'delta-zero';
      var text = (r.change > 0 ? '+' : '') + r.change;
      return '<div class="list-row" style="padding:7px 9px">' +
        '<div class="who"><b style="font-size:12.5px">' + esc(prettyReason(r.reason)) + '</b>' +
        '<span>' + esc(r.detail || '') + ' · ' + fmtAgo(r.createdAt) + '</span></div>' +
        '<span class="' + cls + '">' + text + '</span></div>';
    }).join('');
  }

  function renderNotifications() {
    if (!S.lobby) return;
    var rows = S.lobby.notifications || [];
    var box = $('notifList');
    if (!rows.length) {
      box.innerHTML = '<div class="empty">Nothing yet.</div>';
      return;
    }
    box.innerHTML = rows.map(function (n) {
      return '<div class="note-item' + (n.read ? '' : ' unread') + '"><b>' + esc(n.title) + '</b>' +
        '<span>' + esc(n.body) + ' · ' + fmtAgo(n.createdAt) + '</span></div>';
    }).join('');
  }

  /* ------------------------------------------------- incoming challenge call */
  function showChallengeRing(inv) {
    if (!inv || !inv.id) return;
    /* one ringing popup at a time — a second challenge simply waits in the list */
    if (S.ring) { toast('Another challenge', inv.username + ' (' + inv.rating + ') also wants a game. It is listed under Invitations.', 'info'); return; }
    S.ring = { id: inv.id, username: inv.username, rating: inv.rating, expiresAt: inv.expiresAt };
    $('ringAvatar').textContent = String(inv.username || '?').slice(0, 1).toUpperCase();
    $('ringName').textContent = inv.username;
    $('ringRating').textContent = 'rating ' + inv.rating + ' · rated ' + Math.round(((S.config && S.config.pvpMatchSeconds) || 600) / 60) + '-minute match';
    $('ringPop').hidden = false;
    startRinging();
    $('ringAccept').disabled = false;
    $('ringDecline').disabled = false;
    $('ringAccept').focus();
    tickRingCountdown();
  }

  function tickRingCountdown() {
    var el = $('ringCount');
    if (!el) return;
    if (!S.ring) { el.textContent = ''; return; }
    var left = S.ring.expiresAt ? new Date(S.ring.expiresAt).getTime() - Date.now() : 0;
    if (left <= 0) {
      hideChallengeRing();
      toast('Invitation expired', 'You did not answer in time. Expired invitations carry no penalty.', 'info');
      scheduleLobbyRefresh();
      return;
    }
    el.textContent = 'Ring expires in ' + fmtClock(left);
  }

  function hideChallengeRing() {
    S.ring = null;
    stopRinging();
    $('ringPop').hidden = true;
  }

  function answerChallenge(action) {
    var ring = S.ring;
    if (!ring) return;
    $('ringAccept').disabled = true;
    $('ringDecline').disabled = true;
    stopRinging();
    api('/invitations/' + ring.id + '/respond', { method: 'POST', body: { action: action } })
      .then(function (res) {
        hideChallengeRing();
        if (action === 'accept') {
          toast('Challenge accepted', 'The board is ready — good luck.', 'success');
          if (res.gameId) openGame(res.gameId);
        } else {
          var penalty = (typeof res.penalty === 'number') ? res.penalty : declinePoints();
          toast('Challenge declined', penalty > 0
            ? 'You lost ' + penalty + ' point' + (penalty === 1 ? '' : 's') + '. ' + ring.username + ' was not affected.'
            : 'No points were deducted from you.', 'error');
          loadLobby();
        }
      })
      .catch(function (err) {
        hideChallengeRing();
        toast('Could not answer the challenge', err.message, 'error');
        loadLobby();
      });
  }

  /* ------------------------------------------------------------ match chat */
  function chatKey(msg) {
    return (msg.username || '') + '|' + (msg.at || '') + '|' + (msg.text || '');
  }

  function appendChat(msg) {
    if (!msg || !S.game || msg.gameId !== S.game.gameId) return;
    var log = $('chatLog');
    if (!log) return;
    var key = chatKey(msg);
    if (S.chatSeen[key]) return;
    S.chatSeen[key] = true;
    var row = document.createElement('div');
    row.className = 'chat-msg' + (msg.role === 'spectator' ? ' spectator' : '');
    if (S.user && msg.username === S.user.username) row.className += ' mine';
    var who = document.createElement('b');
    who.textContent = msg.username || 'Someone';
    row.appendChild(who);
    if (msg.role === 'spectator') {
      var tag = document.createElement('span');
      tag.className = 'tag';
      tag.textContent = 'spectator';
      row.appendChild(tag);
    }
    row.appendChild(document.createTextNode(' ' + (msg.text || '')));
    log.appendChild(row);
    while (log.children.length > 60) log.removeChild(log.firstChild);
    log.scrollTop = log.scrollHeight;
  }

  function renderChatHistory(list) {
    var log = $('chatLog');
    if (!log) return;
    log.replaceChildren();
    S.chatSeen = {};
    var intro = document.createElement('div');
    intro.className = 'chat-msg system';
    intro.textContent = S.spectating
      ? 'You are watching. Suggestions and commentary here never move a piece.'
      : 'Commentary is shared with your opponent and the audience; it never changes the board.';
    log.appendChild(intro);
    (list || []).forEach(function (entry) {
      appendChat({ gameId: S.game && S.game.gameId, username: entry.username, role: entry.role, text: entry.text, at: entry.at });
    });
  }

  function sendChat(event) {
    if (event) event.preventDefault();
    var input = $('chatInput');
    var g = S.game;
    if (!g || !input) return;
    var text = (input.value || '').trim();
    if (!text) return;
    if (text.length > 240) text = text.slice(0, 240);
    input.value = '';
    socketEmit('game:chat', { gameId: g.gameId, text: text }, function (res) {
      if (!res || !res.ok) {
        toast('Message not sent', (res && res.error) || 'Please try again.', 'error');
        input.value = text;
      }
    });
  }

  /* ----------------------------------------------------------- match clock */
  function syncClock(state) {
    if (!state || !state.clockEndsAt) {
      S.clockDeadline = 0;
      $('matchClock').hidden = true;
      return;
    }
    var endsAt = new Date(state.clockEndsAt).getTime();
    var skew = (state.serverTime || Date.now()) - Date.now();
    S.clockDeadline = endsAt - skew;
    $('matchClock').hidden = false;
    tickClock();
  }

  function tickClock() {
    var el = $('matchClock');
    if (!el) return;
    if (!S.clockDeadline) { el.hidden = true; return; }
    var left = S.clockDeadline - Date.now();
    if (left < 0) left = 0;
    el.hidden = false;
    el.textContent = fmtClock(left);
    el.classList.toggle('low', left > 0 && left <= 60000);
    if (left === 0 && S.game && S.game.status === 'active') {
      el.textContent = 'time up';
      scheduleLobbyRefresh();
    }
  }

  /* ----------------------------------------------------------- game display */
  function applyGameState(state) {
    var previous = S.game;
    var isNewGame = !previous || previous.gameId !== state.gameId;
    S.spectating = Boolean(state.spectating) || state.role === 'spectator' || !state.you;
    var gainedCapture = false;
    if (!isNewGame && state.moves && previous.moves && state.moves.length > previous.moves.length) {
      var lastMove = state.moves[state.moves.length - 1];
      gainedCapture = Boolean(lastMove && lastMove.captured);
    }
    S.game = state;
    S.awaiting = false;
    if (isNewGame) {
      S.resultShown = null;
      S.selected = null;
      if (!S.flipManual) S.flipped = state.you === 'b';
      $('resultSlot').innerHTML = '';
      S.spectatorCount = state.spectators || 0;
      renderChatHistory(state.chat || []);
      showView('viewGame');
      if (state.you) socketEmit('game:join', { gameId: state.gameId }, function () {});
    } else {
      playCue(gainedCapture ? 'capture' : 'move');
    }
    if (Array.isArray(state.chat)) (state.chat || []).forEach(appendChat);
    syncClock(state);
    renderGame();
    if (state.status === 'finished' && S.resultShown !== state.gameId) {
      S.resultShown = state.gameId;
      if (!S.spectating) showResult(state, (state.ratingChanges && state.ratingChanges[state.you]) || 0, '');
      else toast('Match finished', 'The game has ended. Thanks for watching.', 'info');
    }
  }

  function renderGame() {
    var g = S.game;
    if (!g) return;
    var pieces = parseFen(g.fen);
    var files = S.flipped ? 'hgfedcba' : 'abcdefgh';
    var ranks = S.flipped ? [1, 2, 3, 4, 5, 6, 7, 8] : [8, 7, 6, 5, 4, 3, 2, 1];
    var dests = (S.selected && g.legal && g.legal[S.selected]) || [];
    var board = $('board');
    board.classList.toggle('readonly', S.spectating);
    var frag = document.createDocumentFragment();
    var myTurn = g.status === 'active' && g.turn === g.you;
    var topColor = S.flipped ? 'w' : 'b';
    var bottomColor = S.flipped ? 'b' : 'w';

    for (var ri = 0; ri < 8; ri += 1) {
      for (var fi = 0; fi < 8; fi += 1) {
        var file = files.charAt(fi);
        var rank = ranks[ri];
        var square = file + rank;
        var piece = pieces[square];
        var isDark = ((file.charCodeAt(0) - 97 + rank) % 2) === 1;
        var btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'square ' + (isDark ? 'dark' : 'light');
        btn.setAttribute('data-square', square);
        var label = square + ', ' + (piece
          ? (piece.color === 'w' ? 'white ' : 'black ') + (BOOT.pieceNames[piece.type] || piece.type)
          : 'empty');
        if (g.lastMove && (g.lastMove.from === square || g.lastMove.to === square)) btn.className += ' last';
        if (S.selected === square) btn.className += ' selected';
        if (g.kingSquare === square) btn.className += ' check';
        var showDot = false;
        var showRing = false;
        for (var d = 0; d < dests.length; d += 1) {
          if (dests[d].to === square) {
            label += ', legal move';
            if (dests[d].capture) showRing = true; else showDot = true;
          }
        }
        if (showDot || showRing) {
          var marker = document.createElement('span');
          marker.className = 'legal' + (showRing ? ' capture' : '');
          btn.appendChild(marker);
        }
        btn.setAttribute('aria-label', label);
        if (piece) btn.appendChild(pieceImg(piece.color, piece.type));
        if (fi === 0) {
          var rc = document.createElement('span');
          rc.className = 'coord rank';
          rc.textContent = rank;
          btn.appendChild(rc);
        }
        if (ri === 7) {
          var fc = document.createElement('span');
          fc.className = 'coord file';
          fc.textContent = file;
          btn.appendChild(fc);
        }
        frag.appendChild(btn);
      }
    }
    board.replaceChildren(frag);

    var topPlayer = g.players[topColor];
    var bottomPlayer = g.players[bottomColor];
    $('topName').textContent = topPlayer.username;
    $('topRating').textContent = topPlayer.isAi ? 'AI · ' + (g.aiDifficulty || 'practice') : (topPlayer.rating || 0) + ' rating';
    $('bottomName').textContent = bottomPlayer.username + (g.you === bottomColor ? ' (you)' : '');
    $('bottomRating').textContent = bottomPlayer.isAi ? 'AI · ' + (g.aiDifficulty || 'practice') : (bottomPlayer.rating || 0) + ' rating';
    $('topBar').classList.toggle('active', g.status === 'active' && g.turn === topColor);
    $('bottomBar').classList.toggle('active', g.status === 'active' && g.turn === bottomColor);
    $('topDot').className = 'dot' + (g.status === 'active' && g.turn === topColor ? '' : ' off');
    $('bottomDot').className = 'dot' + (g.status === 'active' && g.turn === bottomColor ? '' : ' off');

    var order = ['q', 'r', 'b', 'n', 'p'];
    function renderCaptured(el, ownerColor) {
      var list = (g.captured[ownerColor] || []).slice().sort(function (a, b) {
        return order.indexOf(a) - order.indexOf(b);
      });
      var wrap = document.createElement('div');
      wrap.className = 'captured';
      list.forEach(function (type) {
        var img = pieceImg(ownerColor === 'w' ? 'b' : 'w', type);
        img.style.width = '21px';
        img.style.height = '21px';
        wrap.appendChild(img);
      });
      var score = document.createElement('span');
      score.className = 'capscore';
      score.textContent = String(list.length);
      wrap.appendChild(score);
      el.replaceChildren(wrap);
    }
    renderCaptured($('topCaptured'), topColor);
    renderCaptured($('bottomCaptured'), bottomColor);

    var mine = g.you || 'w';
    var theirs = mine === 'w' ? 'b' : 'w';
    $('scoreYouLabel').textContent = S.spectating ? 'White captures' : 'Your captures';
    $('scoreOppLabel').textContent = S.spectating ? 'Black captures' : 'Their captures';
    $('scoreYou').textContent = g.capturePoints[mine] || 0;
    $('scoreOpp').textContent = g.capturePoints[theirs] || 0;
    $('scoreYouDetail').textContent = (g.captured[mine] || []).length + ' pieces captured';
    $('scoreOppDetail').textContent = (g.captured[theirs] || []).length + ' pieces captured';

    var status = $('status');
    status.className = 'status';
    var text;
    if (g.status === 'finished') {
      if (g.result === 'draw') {
        text = 'Draw — ' + prettyReason(g.resultReason);
      } else {
        var winnerName = g.result === 'white' ? g.players.w.username : g.players.b.username;
        text = winnerName + ' wins by ' + prettyReason(g.resultReason);
        if (g.result === g.you) status.className = 'status win';
      }
    } else if (S.spectating) {
      text = 'Watching · ' + (g.turn === 'w' ? 'White' : 'Black') + ' to move' + (g.inCheck ? ' — check!' : '');
      status.className = 'status';
    } else if (S.awaiting) {
      text = 'Sending your move…';
    } else if (myTurn) {
      text = (g.inCheck ? 'Check! ' : '') + 'Your move';
      status.className = g.inCheck ? 'status alert' : 'status';
    } else {
      text = (g.inCheck ? 'Check! ' : '') + (g.turn === 'w' ? 'White' : 'Black') + ' to move' +
        (g.mode === 'ai' ? ' · computer thinking…' : '');
      /* red is reserved for check/errors in the light theme */
      status.className = g.inCheck ? 'status alert' : 'status';
    }
    status.textContent = text;

    var list = $('moveList');
    if (!g.moves.length) {
      list.innerHTML = '<div class="empty">No moves yet. White starts.</div>';
    } else {
      var rows = '';
      for (var i = 0; i < g.moves.length; i += 2) {
        rows += '<div class="move-row"><span class="num">' + (Math.floor(i / 2) + 1) + '.</span>' +
          '<span class="san' + (i === g.moves.length - 1 ? ' last' : '') + '">' + esc(g.moves[i].san) + '</span>' +
          '<span class="san' + (i + 1 === g.moves.length - 1 ? ' last' : '') + '">' +
          esc(g.moves[i + 1] ? g.moves[i + 1].san : '') + '</span></div>';
      }
      list.innerHTML = rows;
      list.scrollTop = list.scrollHeight;
    }
    $('moveCount').textContent = g.moves.length + ' plies';
    $('gameModePill').textContent = S.spectating
      ? 'Spectating'
      : (g.mode === 'ai' ? 'Practice · ' + (g.aiDifficulty || 'ai') : 'Rated multiplayer');
    $('gameMeta').textContent = g.mode === 'ai'
      ? ((S.config && S.config.aiRated) ? 'AI games are rated' : 'AI games do not change your rating')
      : 'Winner takes only the points they captured';

    var banner = $('drawOfferBanner');
    if (g.status === 'active' && g.drawOfferBy && g.drawOfferBy !== g.you) {
      banner.hidden = false;
      $('drawOfferText').textContent = g.players[g.drawOfferBy].username + ' offers a draw.';
    } else {
      banner.hidden = true;
    }
    var canAct = g.status === 'active' && Boolean(g.you) && !S.spectating;
    $('playerActions').hidden = S.spectating;
    $('spectatorActions').hidden = !S.spectating;
    $('btnResign').disabled = !canAct;
    $('btnDraw').disabled = !canAct || Boolean(g.drawOfferBy);
    $('btnLeave').disabled = g.status !== 'active' || S.spectating;
    $('coachPanel').hidden = !(S.coachOpen && S.config && S.config.coachEnabled);
    var chatHint = $('chatHint');
    if (chatHint) chatHint.textContent = S.spectating ? 'you are in the audience' : 'shared with the table';
    renderSpectatorMeta();
    renderWatchPill();
  }

  function renderSpectatorMeta() {
    var g = S.game;
    var banner = $('spectatorBanner');
    if (!banner) return;
    banner.hidden = !S.spectating;
    if (!S.spectating || !g) return;
    var count = S.spectatorCount || (g.spectators || 0);
    $('spectatorText').textContent = 'Watching ' + g.players.w.username + ' (white) vs ' + g.players.b.username +
      ' (black) · ' + count + ' spectator' + (count === 1 ? '' : 's') + '. The board is read-only here.';
    var hint = $('chatHint');
    if (hint) hint.textContent = 'you are in the audience';
  }

  /* Players see a small "N watching" pill; spectators see the audience banner. */
  function renderWatchPill() {
    var pill = $('watchPill');
    if (!pill || !S.game) return;
    var count = S.spectatorCount || S.game.spectators || 0;
    pill.hidden = S.spectating || count <= 0;
    pill.textContent = count + ' watching';
  }

  function showResult(state, delta, summary) {
    var title = state.result === 'draw' ? 'Draw' : state.result === state.you ? 'You won' : 'You lost';
    var reason = prettyReason(state.resultReason);
    var sign = delta > 0 ? '+' : '';
    var deltaText = state.rated ? (sign + delta + ' rating') : 'Practice game · rating unchanged';
    var mine = state.capturePoints[state.you] || 0;
    var theirs = state.capturePoints[state.you === 'w' ? 'b' : 'w'] || 0;
    var extra = state.result === 'draw'
      ? 'No points are transferred on a draw.'
      : 'Captures: you ' + mine + ' · opponent ' + theirs;

    $('resultSlot').innerHTML = '<div class="result-banner"><h4>' + esc(title) + '</h4>' +
      '<div class="tiny muted">' + esc(summary || reason) + '</div>' +
      '<div class="delta">' + esc(deltaText) + '</div>' +
      '<div class="tiny muted">' + esc(extra) + '</div></div>';

    $('resultTitle').textContent = title + ' — ' + reason;
    $('resultBody').innerHTML = '<p><b style="color:var(--teal-deep)">' + esc(deltaText) + '</b></p>' +
      '<p>' + esc(extra) + '</p>' +
      (state.mode === 'ai'
        ? '<p class="tiny muted">Practice games do not move your rating unless the server operator enables AI_GAMES_AFFECT_RATING.</p>'
        : '');
    var rematch = $('resultRematch');
    rematch.textContent = state.mode === 'ai' ? 'New AI game' : 'Back to lobby';
    rematch.setAttribute('data-mode', state.mode || 'multiplayer');
    if (!$('resultDialog').open) $('resultDialog').showModal();
  }

  function openGame(gameId) {
    showView('viewGame');
    setPath('/game');
    if (!S.socket) {
      showView('viewLobby');
      return;
    }
    S.spectating = false;
    socketEmit('game:join', { gameId: gameId }, function (res) {
      if (!res || !res.ok) {
        /* Not a player? The same endpoint tells us so — try the audience seat. */
        if (res && res.code && /spectat|not_player|not_a_player|not-your/i.test(res.code)) {
          spectateGame(gameId);
          return;
        }
        toast('Cannot open that match', (res && res.error) || 'Please try again.', 'error');
        showView('viewLobby');
        loadLobby();
        return;
      }
      applyGameState(res.game);
    });
  }

  /* Watch a live match without touching it. */
  function spectateGame(gameId) {
    showView('viewGame');
    setPath('/game');
    S.spectating = true;
    socketEmit('spectate:join', { gameId: gameId }, function (res) {
      if (!res || !res.ok) {
        S.spectating = false;
        toast('Cannot watch that match', (res && res.error) || 'Please try again.', 'error');
        showView('viewLobby');
        loadLobby();
        return;
      }
      S.spectatorCount = (res.game && res.game.spectators) || 0;
      applyGameState(res.game);
      toast('Watching live', 'Chat with the players — the board stays untouched.', 'info');
    });
  }

  function leaveGameView() {
    var g = S.game;
    if (S.spectating) {
      if (g) socketEmit('spectate:leave', { gameId: g.gameId }, function () {});
      S.spectating = false;
      S.game = null;
      S.clockDeadline = 0;
      $('matchClock').hidden = true;
      showView('viewLobby');
      loadLobby();
      return;
    }
    if (g && g.status === 'active') {
      confirmAction('Leave this match?',
        'Walking out of a live match counts as a forfeit: you lose ' + forfeitPoints() +
        ' points and your opponent wins. Your seat stays saved if you simply return to the lobby instead.',
        'Forfeit and leave',
        function () {
          socketEmit('game:leave', { gameId: g.gameId }, function (res) {
            if (res && res.ok) {
              toast('Match left', res.penalty > 0
                ? 'You forfeited and lost ' + res.penalty + ' points.'
                : 'Practice game closed. No rating change.', res.penalty > 0 ? 'error' : 'info');
            } else {
              toast('Could not leave the match', (res && res.error) || 'Please try again.', 'error');
            }
            S.game = null;
            $('matchClock').hidden = true;
            showView('viewLobby');
            loadLobby();
          });
        });
      return;
    }
    S.game = null;
    $('matchClock').hidden = true;
    showView('viewLobby');
    loadLobby();
  }

  function submitMove(from, to, promotion) {
    var g = S.game;
    if (!g) return;
    S.selected = null;
    S.awaiting = true;
    renderGame();
    socketEmit('game:move', { gameId: g.gameId, from: from, to: to, promotion: promotion || undefined }, function (res) {
      if (!res || !res.ok) {
        S.awaiting = false;
        renderGame();
        toast('Move rejected', (res && res.error) || 'Please try again.', 'error');
      }
    });
  }

  function onSquareClick(square) {
    var g = S.game;
    if (!g || g.status !== 'active' || S.awaiting || !g.you) return;
    if (g.turn !== g.you) {
      toast('Not your turn', 'Wait for your opponent to move.', 'info');
      return;
    }
    if (S.selected === square) {
      S.selected = null;
      renderGame();
      return;
    }
    var dests = (g.legal && g.legal[S.selected]) || [];
    var matches = dests.filter(function (d) { return d.to === square; });
    if (S.selected && matches.length) {
      var needsPromotion = false;
      for (var i = 0; i < matches.length; i += 1) if (matches[i].promotion) needsPromotion = true;
      if (needsPromotion) {
        S.promo = { from: S.selected, to: square };
        openPromotion();
        return;
      }
      submitMove(S.selected, square, null);
      return;
    }
    var pieces = parseFen(g.fen);
    var piece = pieces[square];
    if (piece && piece.color === g.you) {
      S.selected = square;
      renderGame();
      return;
    }
    S.selected = null;
    renderGame();
  }

  function openPromotion() {
    var box = $('promoChoices');
    box.innerHTML = '';
    var color = S.game && S.game.you ? S.game.you : 'w';
    ['q', 'r', 'b', 'n'].forEach(function (type) {
      var btn = document.createElement('button');
      btn.type = 'button';
      btn.title = 'Promote to ' + (BOOT.pieceNames[type] || type);
      btn.setAttribute('aria-label', btn.title);
      btn.appendChild(pieceImg(color, type));
      btn.addEventListener('click', function () {
        var move = S.promo;
        S.promo = null;
        $('promotionDialog').close();
        if (move) submitMove(move.from, move.to, type);
      });
      box.appendChild(btn);
    });
    if (!$('promotionDialog').open) $('promotionDialog').showModal();
  }

  function confirmAction(title, body, okLabel, onOk) {
    $('confirmTitle').textContent = title;
    $('confirmBody').textContent = body;
    var ok = $('confirmOk');
    ok.textContent = okLabel || 'Confirm';
    var fresh = ok.cloneNode(true);
    ok.replaceWith(fresh);
    fresh.addEventListener('click', function () {
      $('confirmDialog').close();
      onOk();
    });
    if (!$('confirmDialog').open) $('confirmDialog').showModal();
  }

  /* ---------------------------------------------------------------- wiring */
  function wire() {
    $('splashMark').innerHTML = inlinePiece('w', 'n', 54);
    $('authMark').innerHTML = inlinePiece('w', 'k', 44);
    $('lobbyMark').innerHTML = inlinePiece('w', 'k', 34);
    $('ghostPiece').src = pieceUrl('b', 'q');

    $('tabLogin').addEventListener('click', function () { switchAuthTab('login'); });
    $('tabSignup').addEventListener('click', function () { switchAuthTab('signup'); });
    $('loginForm').addEventListener('submit', doLogin);
    $('signupForm').addEventListener('submit', doSignup);

    $('btnLogout').addEventListener('click', function () {
      confirmAction('Sign out?', 'Your session will end. Any active match stays saved on the server and can be resumed from the lobby.', 'Sign out', doLogout);
    });

    $('btnSound').addEventListener('click', function () {
      S.sound = !S.sound;
      $('btnSound').textContent = 'Sound: ' + (S.sound ? 'on' : 'off');
      if (S.sound) playCue('move');
    });

    $('difficultySeg').addEventListener('click', function (event) {
      var btn = event.target.closest('[data-diff]');
      if (!btn) return;
      S.diff = btn.getAttribute('data-diff');
      Array.prototype.forEach.call($('difficultySeg').children, function (child) {
        child.classList.toggle('active', child === btn);
      });
    });

    $('btnPlayAi').addEventListener('click', function () {
      var btn = $('btnPlayAi');
      btn.disabled = true;
      api('/games/ai', { method: 'POST', body: { difficulty: S.diff, color: $('aiColor').value } })
        .then(function (res) { openGame(res.gameId); })
        .catch(function (err) { toast('Could not start the AI game', err.message, 'error'); })
        .then(function () { btn.disabled = false; });
    });

    $('btnQuickMatch').addEventListener('click', function () {
      if (!S.socket) return;
      if (S.matchmaking) {
        socketEmit('matchmaking:leave', {}, function () {
          S.matchmaking = false;
          $('btnQuickMatch').textContent = 'Find opponent';
          $('matchStatus').textContent = '';
        });
        return;
      }
      socketEmit('matchmaking:join', {}, function (res) {
        if (!res || !res.ok) {
          toast('Matchmaking', (res && res.error) || 'Please try again.', 'error');
          return;
        }
        S.matchmaking = true;
        $('btnQuickMatch').textContent = 'Cancel search';
        $('matchStatus').textContent = 'Searching for an opponent…';
      });
    });

    function sendInvite(username, button) {
      var name = (username || $('inviteUsername').value || '').trim();
      if (!name) {
        toast('Invitation', 'Enter a username first.', 'error');
        return;
      }
      if (button) button.disabled = true;
      api('/invitations', { method: 'POST', body: { toUsername: name } })
        .then(function (res) {
          if (res.autoAccepted && res.gameId) {
            toast('Match started', 'You both wanted this game — the board is ready.', 'success');
            openGame(res.gameId);
            return;
          }
          toast('Invitation sent', 'Waiting for ' + name + ' to respond.', 'success');
          $('inviteUsername').value = '';
          loadLobby();
        })
        .catch(function (err) { toast('Invitation failed', err.message, 'error'); })
        .then(function () { if (button) button.disabled = false; });
    }
    $('btnSendInvite').addEventListener('click', function () { sendInvite(null, $('btnSendInvite')); });
    $('inviteUsername').addEventListener('keydown', function (event) {
      if (event.key === 'Enter') { event.preventDefault(); sendInvite(null, $('btnSendInvite')); }
    });

    $('inviteBox').addEventListener('click', function (event) {
      var accept = event.target.closest('[data-accept]');
      var reject = event.target.closest('[data-reject]');
      var cancel = event.target.closest('[data-cancel]');
      if (accept) {
        accept.disabled = true;
        api('/invitations/' + accept.getAttribute('data-accept') + '/respond', { method: 'POST', body: { action: 'accept' } })
          .then(function (res) {
            toast('Invitation accepted', 'Starting the match…', 'success');
            if (res.gameId) openGame(res.gameId);
          })
          .catch(function (err) { toast('Could not accept', err.message, 'error'); loadLobby(); });
        return;
      }
      if (reject) {
        var id = reject.getAttribute('data-reject');
        var name = reject.getAttribute('data-name') || 'this player';
        var cost = declinePoints();
        confirmAction('Decline this challenge?',
          'Declining costs you ' + cost + ' rating point' + (cost === 1 ? '' : 's') + ' (never below 0). ' +
          name + ' is not affected at all.',
          'Decline and lose ' + cost,
          function () {
            api('/invitations/' + id + '/respond', { method: 'POST', body: { action: 'reject' } })
              .then(function (res) {
                var charged = (res && typeof res.penalty === 'number') ? res.penalty : cost;
                if (S.ring && S.ring.id === id) hideChallengeRing();
                toast('Challenge declined', charged > 0
                  ? 'You lost ' + charged + ' point' + (charged === 1 ? '' : 's') + '.'
                  : 'No points were deducted from you.', charged > 0 ? 'error' : 'info');
                loadLobby();
              })
              .catch(function (err) { toast('Could not decline', err.message, 'error'); loadLobby(); });
          });
        return;
      }
      if (cancel) {
        api('/invitations/' + cancel.getAttribute('data-cancel') + '/cancel', { method: 'POST' })
          .then(function () { toast('Invitation cancelled', 'Cancelled invitations never carry a penalty.', 'info'); loadLobby(); })
          .catch(function (err) { toast('Could not cancel', err.message, 'error'); });
      }
    });

    $('playersList').addEventListener('click', function (event) {
      var btn = event.target.closest('[data-invite]');
      if (btn) sendInvite(btn.getAttribute('data-invite'), btn);
    });

    $('ringAccept').addEventListener('click', function () { answerChallenge('accept'); });
    $('ringDecline').addEventListener('click', function () { answerChallenge('reject'); });
    $('ringPop').addEventListener('click', function (event) {
      /* clicking the backdrop keeps the call ringing; only the buttons answer */
      if (event.target === $('ringPop')) event.stopPropagation();
    });
    document.addEventListener('keydown', function (event) {
      if (!S.ring || $('ringPop').hidden) return;
      if (event.key === 'Escape') { event.preventDefault(); answerChallenge('reject'); }
      if (event.key === 'Enter') { event.preventDefault(); answerChallenge('accept'); }
    });

    $('chatForm').addEventListener('submit', sendChat);

    $('btnLeave').addEventListener('click', function () {
      leaveGameView();
    });
    $('btnLeaveSpec').addEventListener('click', function () {
      leaveGameView();
    });
    $('btnFlipSpec').addEventListener('click', function () {
      S.flipped = !S.flipped;
      S.flipManual = true;
      renderGame();
    });

    $('liveList').addEventListener('click', function (event) {
      var watch = event.target.closest('[data-spectate]');
      var resume = event.target.closest('[data-resume]');
      if (watch) { spectateGame(watch.getAttribute('data-spectate')); return; }
      if (resume) { openGame(resume.getAttribute('data-resume')); }
    });

    $('activeList').addEventListener('click', function (event) {
      var btn = event.target.closest('[data-resume]');
      if (btn) openGame(btn.getAttribute('data-resume'));
    });

    $('btnReadAll').addEventListener('click', function () {
      api('/notifications/read', { method: 'POST' }).then(function () { loadLobby(); }).catch(function () {});
    });

    $('board').addEventListener('click', function (event) {
      var square = event.target.closest('[data-square]');
      if (square) onSquareClick(square.getAttribute('data-square'));
    });

    $('btnBack').addEventListener('click', function () {
      var g = S.game;
      if (S.spectating) {
        if (g) socketEmit('spectate:leave', { gameId: g.gameId }, function () {});
        S.spectating = false;
        S.game = null;
        $('matchClock').hidden = true;
        showView('viewLobby');
        loadLobby();
        return;
      }
      if (g && g.status === 'active') {
        confirmAction('Return to the lobby?',
          'Your match stays saved on the server and the clock keeps running — you can resume it from Active matches. ' +
          'If you close the tab for longer than the grace period, the match is forfeited and you lose ' + forfeitPoints() + ' points.',
          'Back to lobby', function () {
            showView('viewLobby');
            loadLobby();
          });
        return;
      }
      showView('viewLobby');
      loadLobby();
    });

    $('btnFlip').addEventListener('click', function () {
      S.flipped = !S.flipped;
      S.flipManual = true;
      renderGame();
    });

    $('btnResign').addEventListener('click', function () {
      var g = S.game;
      if (!g) return;
      var oppPoints = g.capturePoints[g.you === 'w' ? 'b' : 'w'] || 0;
      confirmAction('Resign this game?', 'Resigning ends the match immediately: your opponent receives only the ' + oppPoints +
        ' capture point(s) they actually earned — resigning carries no extra penalty.', 'Resign', function () {
        socketEmit('game:resign', { gameId: g.gameId }, function (res) {
          if (!res || !res.ok) toast('Could not resign', (res && res.error) || '', 'error');
        });
      });
    });

    $('btnDraw').addEventListener('click', function () {
      var g = S.game;
      if (!g) return;
      socketEmit('game:draw:offer', { gameId: g.gameId }, function (res) {
        if (!res || !res.ok) {
          toast('Draw offer', (res && res.error) || 'Please try again.', 'error');
          return;
        }
        toast('Draw offered', 'Your opponent can accept or decline.', 'info');
      });
    });

    $('btnAcceptDraw').addEventListener('click', function () {
      var g = S.game;
      if (!g) return;
      socketEmit('game:draw:respond', { gameId: g.gameId, accept: true }, function (res) {
        if (!res || !res.ok) toast('Draw', (res && res.error) || '', 'error');
      });
    });

    $('btnDeclineDraw').addEventListener('click', function () {
      var g = S.game;
      if (!g) return;
      socketEmit('game:draw:respond', { gameId: g.gameId, accept: false }, function (res) {
        if (!res || !res.ok) toast('Draw', (res && res.error) || '', 'error');
        else toast('Draw declined', 'Play on.', 'info');
      });
    });

    $('btnCoachToggle').addEventListener('click', function () {
      if (!(S.config && S.config.coachEnabled)) {
        toast('Coach unavailable', 'This server has no GROQ_API_KEY configured, so the chess coach is disabled.', 'info');
        return;
      }
      S.coachOpen = !S.coachOpen;
      renderGame();
    });

    $('coachForm').addEventListener('submit', function (event) {
      event.preventDefault();
      var input = $('coachInput');
      var question = input.value.trim();
      var g = S.game;
      if (!question || !g) return;
      var log = $('coachLog');
      var mine = document.createElement('div');
      mine.className = 'coach-msg user';
      mine.textContent = question;
      log.appendChild(mine);
      input.value = '';
      var pending = document.createElement('div');
      pending.className = 'coach-msg';
      pending.textContent = 'Thinking…';
      log.appendChild(pending);
      log.scrollTop = log.scrollHeight;
      api('/coach', { method: 'POST', body: { question: question, fen: g.fen } })
        .then(function (res) { pending.textContent = res.answer; })
        .catch(function (err) {
          pending.textContent = err.message;
          pending.style.color = '#f0a79c';
        })
        .then(function () { log.scrollTop = log.scrollHeight; });
    });

    $('promoCancel').addEventListener('click', function () {
      S.promo = null;
      $('promotionDialog').close();
    });
    $('promotionDialog').addEventListener('cancel', function (event) {
      event.preventDefault();
      S.promo = null;
      $('promotionDialog').close();
    });
    $('confirmCancel').addEventListener('click', function () { $('confirmDialog').close(); });

    $('resultLobby').addEventListener('click', function () {
      $('resultDialog').close();
      showView('viewLobby');
      loadLobby();
    });
    $('resultRematch').addEventListener('click', function () {
      $('resultDialog').close();
      var mode = $('resultRematch').getAttribute('data-mode');
      if (mode === 'ai') {
        api('/games/ai', { method: 'POST', body: { difficulty: S.diff, color: $('aiColor').value } })
          .then(function (res) { openGame(res.gameId); })
          .catch(function (err) {
            toast('Could not start a new game', err.message, 'error');
            showView('viewLobby');
            loadLobby();
          });
      } else {
        showView('viewLobby');
        loadLobby();
      }
    });

    setInterval(function () {
      Array.prototype.forEach.call(document.querySelectorAll('.countdown'), function (el) {
        var target = new Date(el.getAttribute('data-since')).getTime();
        var left = target - Date.now();
        el.textContent = left > 0 ? fmtClock(left) : 'expired';
        if (left <= 0) scheduleLobbyRefresh();
      });
    }, 1000);

    setInterval(function () {
      if (S.socket && S.socket.connected) socketEmit('presence:ping', {}, function () {});
    }, 45000);

    setInterval(tickClock, 500);
    setInterval(function () {
      if (S.ring) tickRingCountdown();
    }, 1000);
  }

  /* ------------------------------------------------------------------ boot */
  wire();
  setConn(false);
  api('/auth/me')
    .then(function (res) {
      S.user = res.user;
      S.config = res.config;
      enterApp(res.activeGameId || null);
    })
    .catch(function (err) {
      /* Retry once: a cold server or a just-set cookie should not log anyone out. */
      if (!err || !err.status || err.status >= 500) {
        setTimeout(function () {
          api('/auth/me')
            .then(function (res) {
              S.user = res.user;
              S.config = res.config;
              enterApp(res.activeGameId || null);
            })
            .catch(function () { showView('viewAuth'); switchAuthTab('login'); });
        }, 400);
        return;
      }
      clearToken();
      showView('viewAuth');
      switchAuthTab('login');
    });
})();
</script>
</body>
</html>`;
}

/* ---------------------------------------------------------------------------
 * Frontend routing.
 *
 * The whole UI is served by this one file, so every navigation — including a
 * hard refresh on /lobby — must answer with the app shell. The order below is
 * deliberate:
 *   1. named shell routes (fast path, no regex),
 *   2. JSON 404 for anything under /api (so a typo'd endpoint never returns HTML),
 *   3. the catch-all wildcard, placed LAST before the error handlers.
 * ------------------------------------------------------------------------- */

function sendAppShell(req, res) {
  res.set('Cache-Control', 'no-store');
  res.type('html').send(renderApp());
}

app.get(['/', '/login', '/signup', '/lobby', '/game', '/play', '/watch'], sendAppShell);

/* Nothing under /api ever reaches the HTML shell: the api router ends with a
 * JSON 404 and its auth guard answers 401 for the rest. */
/* Wildcard fallback for client-side routing (GET/HEAD only, /api excluded). */
app.get(/^(?!\/api(?:\/|$)).*/, sendAppShell);

/* ---------------------------------------------------------------------------
 * SECTION 12 — ERROR HANDLING, STARTUP, SHUTDOWN
 * ------------------------------------------------------------------------- */

/* Central error handler: no stack traces or internal details leak in production. */
app.use((err, req, res, next) => {
  void next;
  const status = err && err.status ? err.status : err instanceof mongoose.Error.ValidationError ? 400 : 500;
  const isClientError = status < 500;
  if (!isClientError) logError(`${req.method} ${req.originalUrl}`, err);
  if (res.headersSent) return;
  if (req.path.startsWith('/api') || req.xhr || (req.get('accept') || '').includes('json')) {
    return res.status(status).json({
      error: isClientError && err.expose !== false ? err.message : 'Something went wrong on the server.',
      code: (err && err.code) || (isClientError ? 'bad_request' : 'internal_error'),
    });
  }
  return res.status(status).type('text').send(isClientError ? err.message : 'Internal server error');
});

/* ---------------------------------------------------------------------------
 * SECTION 13 — BOOTSTRAP
 * ------------------------------------------------------------------------- */

function validateConfig() {
  const fatal = [];
  const warnings = [];
  if (!MONGO_URI) {
    fatal.push('MONGO_URI is missing. Add your MongoDB Atlas connection string to .env (include /chessgame as the database name).');
  } else if (!/^mongodb(\+srv)?:\/\//.test(MONGO_URI)) {
    fatal.push('MONGO_URI must start with mongodb:// or mongodb+srv://');
  }
  if (EPHEMERAL_SECRET) {
    if (IS_PROD) {
      fatal.push('SESSION_SECRET is required in production (set it to a random string of 32+ characters).');
    } else {
      warnings.push('SESSION_SECRET is not set — using a random per-process development secret. Sessions will not survive a restart.');
    }
  } else if (IS_PROD && SESSION_SECRET.length < 32) {
    fatal.push('SESSION_SECRET must be at least 32 characters in production.');
  }
  return { fatal, warnings };
}

/**
 * Decide whether TLS is needed for a connection string.
 *   • an explicit tls=/ssl= parameter in the URI always wins;
 *   • MONGO_TLS=true|false in .env overrides everything (self-hosted servers);
 *   • Atlas hosts (*.mongodb.net, from a rewritten SRV string) need TLS;
 *   • localhost / self-hosted servers usually do not.
 */
function tlsOptionFor(connectionUri) {
  const params = new URLSearchParams(String(connectionUri).split('?')[1] || '');
  if (params.has('tls') || params.has('ssl')) return undefined; // already stated in the URI
  const override = String(process.env.MONGO_TLS || '').trim().toLowerCase();
  if (override === 'true') return true;
  if (override === 'false') return false;
  return /\.mongodb\.net(?::\d+)?(?:[/,?]|$)/i.test(connectionUri);
}

async function connectDatabase(connectionUri) {
  mongoose.set('strictQuery', true);
  const tls = tlsOptionFor(connectionUri);
  await mongoose.connect(connectionUri, {
    dbName: DB_NAME,
    serverSelectionTimeoutMS: 15000,
    maxPoolSize: 20,
    retryWrites: true,
    ...(tls === undefined ? {} : { tls }),
  });
  const { host, name } = mongoose.connection;
  log(`MongoDB connected — ${host}/${name}`);
  await Promise.all([
    User.init(),
    Game.init(),
    Invitation.init(),
    RatingHistory.init(),
    Notification.init(),
    SessionToken.init(),
  ]);
  log('Indexes ready.');
}

let shuttingDown = false;
async function shutdown(signal, exitCode) {
  if (shuttingDown) return;
  shuttingDown = true;
  log(`${signal} received — shutting down…`);
  const forced = setTimeout(() => {
    logError('shutdown', new Error('Forced exit after 12s'));
    process.exit(exitCode || 1);
  }, 12000);
  forced.unref();
  try {
    clearInterval(invitationSweeper);
    clearInterval(gameSweeper);
    clearInterval(presenceJanitor);
    clearInterval(clockSweeper);
    for (const timer of disconnectForfeitTimers.values()) clearTimeout(timer);
    disconnectForfeitTimers.clear();
    if (io) {
      io.disconnectSockets(true);
      await new Promise((resolve) => io.close(resolve));
    }
    await new Promise((resolve) => server.close(resolve));
    await mongoose.connection.close(false);
    clearTimeout(forced);
    log('Shutdown complete.');
    process.exit(exitCode || 0);
  } catch (err) {
    logError('shutdown', err);
    process.exit(1);
  }
}

async function start() {
  const { fatal, warnings } = validateConfig();
  warnings.forEach((w) => console.warn(`[config] ${w}`));
  fatal.forEach((f) => console.error(`[config] ${f}`));
  if (fatal.length) {
    console.error('\nGrandmaster cannot start until the configuration above is fixed. See .env.example.');
    process.exit(1);
  }

  /* Resolve mongodb+srv through the system resolver, then public DNS, then DoH. */
  let connectionUri = MONGO_URI;
  let resolved;
  try {
    resolved = await resolveMongoUri(MONGO_URI);
    connectionUri = resolved.uri;
    if (resolved.unresolved) {
      console.warn(
        '[dns] Could not resolve the SRV record by any method. Attempting the connection anyway…'
      );
    }
  } catch (err) {
    logError('DNS resolution', err);
  }

  try {
    await connectDatabase(connectionUri);
  } catch (err) {
    logError('MongoDB connection failed', err);
    const advice = mongoFailureAdvice(err);
    console.error('\nCould not reach MongoDB.');
    for (const line of advice) console.error(`  ${line}`);
    if (resolved && resolved.unresolved) {
      console.error(
        '\n  The SRV lookup for this cluster failed on every resolver, including DNS-over-HTTPS.',
        '\n  Use the standard connection string from Atlas → Connect → Drivers (it starts',
        '\n  with mongodb:// and lists three hosts) as MONGO_URI.'
      );
    }
    console.error('');
    process.exit(1);
  }

  /* The database is reachable, so it is safe to persist sessions there. */
  try {
    sessionStore.attach(createMongoSessionStore(connectionUri));
    log('Session store ready (MongoDB).');
  } catch (err) {
    logError('session store', err);
    console.error('Could not initialise the MongoDB session store. Aborting.');
    process.exit(1);
  }

  server.listen(PORT, '0.0.0.0', () => {
    log(`Grandmaster listening on ${PUBLIC_URL || `http://localhost:${PORT}`} (${NODE_ENV}) port ${PORT}`);
    log(
      `Auth transport: session cookie (secure=${COOKIE_SECURE === 'auto' ? 'auto — sent only over HTTPS' : COOKIE_SECURE}) ` +
        `+ bearer-token fallback · trust proxy=${JSON.stringify(TRUST_PROXY_VALUE)}`
    );
    if (IS_PROD && COOKIE_SECURE === true && TRUST_PROXY_VALUE === false) {
      warn(
        'COOKIE_SECURE=true while no reverse proxy is trusted: if this server is reached over plain HTTP the ' +
          'browser will refuse the session cookie. Signs of that are players who sign up and stay on the sign-in ' +
          'screen. Serve over HTTPS (with TRUST_PROXY=1) or set COOKIE_SECURE=auto/false.'
      );
    }
    log(
      `Rating model: start ${START_RATING} · capture values ${JSON.stringify(PIECE_VALUES)} · ` +
        `decline penalty ${DECLINE_PENALTY} (paid by the declining player) · forfeit penalty ${FORFEIT_PENALTY} · ` +
        `live match ${Math.round(PVP_MATCH_SECONDS / 60)} min (material decides when time runs out)`
    );
    log(`AI games affect ratings: ${AI_GAMES_AFFECT_RATING}`);
  });

  server.on('error', (err) => {
    if (err.code === 'EADDRINUSE') {
      console.error(`Port ${PORT} is already in use. Set PORT to a free port and restart.`);
    } else {
      logError('http server', err);
    }
    process.exit(1);
  });
}

process.on('unhandledRejection', (reason) => {
  logError('unhandledRejection', reason instanceof Error ? reason : new Error(String(reason)));
});
process.on('uncaughtException', (err) => {
  logError('uncaughtException', err);
  shutdown('uncaughtException', 1).catch(() => process.exit(1));
});
process.on('SIGTERM', () => shutdown('SIGTERM', 0).catch(() => process.exit(0)));
process.on('SIGINT', () => shutdown('SIGINT', 0).catch(() => process.exit(0)));

/**
 * Diagnostic mode: `node server.js --check-dns`
 * Shows what this machine can and cannot resolve, then exits. No credentials
 * are ever printed.
 */
async function checkDns() {
  const { fatal } = validateConfig();
  const uri = MONGO_URI;
  const parsed = parseSrvUri(uri);

  console.log('Grandmaster DNS diagnostics');
  console.log('──────────────────────────────────────────────');
  if (!uri) {
    console.log('MONGO_URI is not set — add it to .env first.');
    return 1;
  }
  if (fatal.length) fatal.forEach((line) => console.log(`[config] ${line}`));
  console.log(`MONGO_URI scheme      : ${isSrvUri(uri) ? 'mongodb+srv (needs an SRV lookup)' : 'mongodb (no SRV lookup needed)'}`);
  if (!parsed) {
    console.log('Could not parse MONGO_URI as a mongodb+srv string.');
    return 1;
  }
  console.log(`Cluster host          : ${parsed.host}`);
  console.log(`Database              : ${parsed.database || '(none, will use ' + DB_NAME + ')'}`);
  console.log(`System DNS servers    : ${dns.getServers().join(', ') || '(none reported)'}`);
  console.log(`Fallback DNS servers  : ${configuredDnsServers().join(', ')}`);
  console.log('');

  let ok = false;
  const target = SRV_PREFIX + parsed.host;
  try {
    const records = await probeSrv(parsed.host);
    console.log(`1. System resolver    : OK — ${records.map((r) => `${r.name}:${r.port}`).join(', ')}`);
    ok = true;
  } catch (err) {
    console.log(`1. System resolver    : FAILED (${err.code || err.message})`);
  }

  if (!ok) {
    const previous = dns.getServers();
    try {
      dns.setServers(configuredDnsServers());
      const records = await probeSrv(parsed.host);
      console.log(`2. Fallback DNS       : OK — ${records.map((r) => `${r.name}:${r.port}`).join(', ')}`);
      ok = true;
    } catch (err) {
      console.log(`2. Fallback DNS       : FAILED (${err.code || err.message})`);
      try {
        dns.setServers(previous);
      } catch (ignored) {
        /* ignore */
      }
    }
  }

  if (!ok) {
    const envHosts = hostsFromEnv();
    if (envHosts) {
      console.log(`3. MONGO_SRV_HOSTS    : OK — ${envHosts.join(', ')}`);
      ok = true;
    } else {
      console.log('3. MONGO_SRV_HOSTS    : not configured');
    }
  }

  if (!ok) {
    const viaHttps = await resolveSrvOverHttps(parsed.host);
    if (viaHttps) {
      console.log(`4. DNS over HTTPS     : OK — ${viaHttps.hosts.join(', ')}`);
      ok = true;
    } else {
      console.log('4. DNS over HTTPS     : FAILED (no answer from Google or Cloudflare)');
    }
  }

  console.log('');
  if (ok) {
    console.log('Verdict: the server can resolve your cluster and will connect.');
    console.log('         Run `node server` to start the app.');
  } else {
    console.log(`Verdict: ${target} cannot be resolved on this machine.`);
    console.log('Use one of these, then run the diagnostic again:');
    console.log('   • Add DNS_SERVERS=8.8.8.8,1.1.1.1 to .env');
    console.log('   • Windows: set the adapter DNS to 8.8.8.8 / 1.1.1.1, then `ipconfig /flushdns`');
    console.log('   • Paste the three hosts from Atlas → Connect → Drivers into MONGO_SRV_HOSTS');
    console.log('   • Or use the mongodb:// (non-SRV) string from Atlas as MONGO_URI');
  }
  return ok ? 0 : 1;
}

if (require.main === module) {
  if (process.argv.includes('--check-dns')) {
    checkDns()
      .then((code) => process.exit(code))
      .catch((err) => {
        logError('check-dns', err);
        process.exit(1);
      });
  } else {
    start();
  }
}

module.exports = {
  app,
  server,
  start,
  /* exported for diagnostics/tests */
  resolveMongoUri,
  parseSrvUri,
  checkDns,
  tlsOptionFor,
  buildDirectUri,
  resolveSrvOverHttps,
  mongoFailureAdvice,
};
