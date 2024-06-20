const n = 500;
function f(x) {
  if (x === 0) return 1;
  else return f(x-1) * x;
}
function g(x) {
  if (x === 0) return 1;
  else return f(n) * g(x-1);
}
function h(x) {
  if (x === 0) return 1;
  else return g(n) * h(x-1);
}
export function main() {
  return h(n);
}
