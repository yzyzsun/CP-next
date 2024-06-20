import { argv } from 'process';
const file = argv[2];

console.time(file);
const module = await import('./' + file);
module.main();
console.timeEnd(file);
