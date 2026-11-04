// index.html 만들기: node build.mjs
import { readFileSync, writeFileSync } from 'node:fs';
const app = readFileSync('src/app.html', 'utf8');
const data = readFileSync('src/data.js', 'utf8');
const conv = readFileSync('src/hwpconv.js', 'utf8');
writeFileSync('index.html', app.replace('/*__DATA__*/', () => data).replace('/*__CONV__*/', () => conv));
console.log('index.html 생성 완료');
