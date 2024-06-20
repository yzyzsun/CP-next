function ints(i) {
  if (i <= 1) return [];
  else return ints(i-1).concat([i]);
}
function primes(nums) {
  function primes_(nums_, i) {
    if (i >= nums_.length) return nums_;
    else {
      function filter(j) {
        var curr = nums_[j];
        if (j >= nums_.length) return [];
        else return (j > i && curr % nums_[i] === 0 ? [] : [curr]).concat(filter(j+1));
      }
      return primes_(filter(0), i+1);
    }
  }
  return primes_(nums, 0);
}
function go(i) {
  if (i === 0) return [];
  else return primes(ints(500)).concat(go(i-1));
}
export function main() {
  return go(1000);
}
