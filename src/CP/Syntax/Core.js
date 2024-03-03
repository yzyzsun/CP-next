"use strict";

export function alloc(e) {
  return { term: e, done: false };
}

export function done(cell) {
  return cell.done;
}

export function read(cell) {
  return cell.term;
}

export function write(v) {
  return function (cell) {
    cell.term = v;
    cell.done = true;
    return v;
  };
}
