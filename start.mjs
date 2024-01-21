import { setFlagsFromString } from 'v8';
setFlagsFromString('--stack-size=864000');
setFlagsFromString('--max-heap-size=32768');

import { argv } from 'process';
const file = argv[2];

console.time(file);
const module = await import('./' + file);
module.main();
console.timeEnd(file);
