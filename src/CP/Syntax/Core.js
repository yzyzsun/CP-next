"use strict";

export function ref(e) {
  return { term: e, done: false };
}

export function done(ref) {
  return ref.done;
}

export function read(ref) {
  return ref.term;
}

export function write(v) {
  return function (ref) {
    ref.term = v;
    ref.done = true;
    return v;
  };
}
