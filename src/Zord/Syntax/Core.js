"use strict";

exports.new = function (e) {
  return { term: e, done: false };
};

exports.done = function (ref) {
  return ref.done;
};

exports.read = function (ref) {
  return ref.term;
};

exports.write = function (v) {
  return function (ref) {
    ref.term = v;
    ref.done = true;
    return v;
  }
};
