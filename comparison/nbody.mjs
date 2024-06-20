const init = [
  { mass: 2e32, x:       0.0, y:       0.0, vx:     0.0, vy:     0.0 },
  { mass: 6e24, x:   6.25e10, y:       0.0, vx:     0.0, vy:  5.66e5 },
  { mass: 6e24, x:  -6.25e10, y:       0.0, vx:     0.0, vy: -5.66e5 },
  { mass: 6e24, x:       0.0, y:   6.25e10, vx: -5.66e5, vy:     0.0 },
  { mass: 6e24, x:       0.0, y:  -6.25e10, vx:  5.66e5, vy:     0.0 },
  { mass: 1e26, x:  2.828e11, y:  2.828e11, vx:     1e5, vy:    -1e5 },
  { mass: 1e26, x:  2.828e11, y: -2.828e11, vx:    -1e5, vy:    -1e5 },
  { mass: 1e26, x: -2.828e11, y: -2.828e11, vx:    -1e5, vy:     1e5 },
  { mass: 1e26, x: -2.828e11, y:  2.828e11, vx:     1e5, vy:     1e5 },
  { mass: 1e16, x: -1.828e11, y:  1.828e11, vx:     1e5, vy:     1e5 }
];
const kGravity = 6.673e-11;
const eps = 0.01;

function force(data, i) {
  function force_(j) {
    if (j >= data.length) return { x: 0, y: 0 };
    else if (j === i) return force_(j+1);
    else {
      const f = force_(j+1);
      const dx = data[j].x - data[i].x;
      const dy = data[j].y - data[i].y;
      const dist = Math.sqrt(dx*dx + dy*dy);
      const fxy = (kGravity * data[j].mass * data[i].mass) / (dist*dist + eps*eps);
      return { x: f.x + fxy * dx / dist, y: f.y + fxy * dy / dist };
    }
  }
  return force_(0);
}

function update(data, dt) {
  function update_(i) {
    if (i >= data.length) return [];
    else {
      const curr = data[i];
      const f = force(data, i);
      const vx = curr.vx + dt * f.x / curr.mass;
      const vy = curr.vy + dt * f.y / curr.mass;
      return [{ mass: curr.mass, x: curr.x + dt * vx, y: curr.y + dt * vy, vx, vy }].concat(update_(i+1));
    }
  }
  return update_(0);
}

function repeat(i) {
  if (i === 0) return init;
  else return update(repeat(i-1), 100);
}
function go(i) {
  if (i === 0) return 0;
  else {
    const head = repeat(1000)[0];
    return Math.sqrt(head.x*head.x + head.y*head.y) + go(i-1);
  }
}
export function main() {
  return go(200);
}
