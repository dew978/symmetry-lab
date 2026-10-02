export const N=20, PAD=36, CELL=30;
export const px=p=>({x:PAD+p.x*CELL,y:PAD+p.y*CELL});
export const same=(a,b)=>Math.abs(a.x-b.x)<1e-7&&Math.abs(a.y-b.y)<1e-7;
export const cross=(a,b,c)=>(b.x-a.x)*(c.y-a.y)-(b.y-a.y)*(c.x-a.x);
export const inside=p=>p.x>=-1e-7&&p.x<=N+1e-7&&p.y>=-1e-7&&p.y<=N+1e-7;
export function reflect(p,axis){const [a,b]=axis,dx=b.x-a.x,dy=b.y-a.y;const t=((p.x-a.x)*dx+(p.y-a.y)*dy)/(dx*dx+dy*dy);return {x:2*(a.x+t*dx)-p.x,y:2*(a.y+t*dy)-p.y};}
export const opposite=(p,c)=>({x:2*c.x-p.x,y:2*c.y-p.y});
export function rotate(p,c,t){const r=Math.PI*t,x=p.x-c.x,y=p.y-c.y;return {x:c.x+x*Math.cos(r)-y*Math.sin(r),y:c.y+x*Math.sin(r)+y*Math.cos(r)};}
export function fold(p,axis,t){const r=reflect(p,axis),q={x:(p.x+r.x)/2,y:(p.y+r.y)/2},v={x:p.x-q.x,y:p.y-q.y},a=axis[0],b=axis[1],dx=b.x-a.x,dy=b.y-a.y,k=((10-a.x)*dx+(10-a.y)*dy)/(dx*dx+dy*dy),anchor={x:a.x+k*dx,y:a.y+k*dy},angle=Math.PI*t,z=Math.hypot(v.x,v.y)*Math.sin(angle),perspective=100/(100-z);return {x:anchor.x+(q.x-anchor.x+v.x*Math.cos(angle))*perspective,y:anchor.y+(q.y-anchor.y+v.y*Math.cos(angle))*perspective};}
export function axisEnd(a,p){return same(a,p)||!inside(p)?null:{x:p.x,y:p.y}};
export function extendAxis([a,b]){const dx=b.x-a.x,dy=b.y-a.y,ts=[];if(dx){ts.push((0-a.x)/dx,(N-a.x)/dx)}if(dy){ts.push((0-a.y)/dy,(N-a.y)/dy)}const ps=ts.map(t=>({x:a.x+t*dx,y:a.y+t*dy})).filter(inside).filter((p,i,all)=>all.findIndex(q=>same(p,q))===i);return ps.slice(0,2);}
export const area=ps=>Math.abs(ps.reduce((s,p,i)=>{const q=ps[(i+1)%ps.length];return s+p.x*q.y-q.x*p.y},0))/2;
function between(a,b,p){return Math.abs(cross(a,b,p))<1e-7&&p.x>=Math.min(a.x,b.x)&&p.x<=Math.max(a.x,b.x)&&p.y>=Math.min(a.y,b.y)&&p.y<=Math.max(a.y,b.y)}
function intersects(a,b,c,d){const ac=cross(a,b,c),ad=cross(a,b,d),ca=cross(c,d,a),cb=cross(c,d,b);return(ac*ad<0&&ca*cb<0)||between(a,b,c)||between(a,b,d)||between(c,d,a)||between(c,d,b)}
export function simple(ps){for(let i=0;i<ps.length;i++)for(let j=i+1;j<ps.length;j++){if(j===i+1||(i===0&&j===ps.length-1))continue;if(intersects(ps[i],ps[(i+1)%ps.length],ps[j],ps[(j+1)%ps.length]))return false}return true}
const compare=(a,b)=>a.y-b.y||a.x-b.x;
const distance=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const length=ps=>ps.slice(1).reduce((sum,p,i)=>sum+distance(ps[i],p),0);
// Grow a path from the globally closest pairs, at either end of each fragment.
// Unlike a nearest-neighbor walk, the first point does not force a long diagonal.
export function nearestPath(points,start=null,end=null){
 const ps=points.slice().sort(compare),n=ps.length;if(n<2)return ps;
 const si=start?ps.findIndex(p=>same(p,start)):-1,ei=end?ps.findIndex(p=>same(p,end)):-1;
 const roots=ps.map((_,i)=>i),sizes=Array(n).fill(1),links=ps.map(()=>[]),edges=[];
 const root=i=>{while(roots[i]!==i){roots[i]=roots[roots[i]];i=roots[i]}return i};
 for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)edges.push({i,j,d:(ps[i].x-ps[j].x)**2+(ps[i].y-ps[j].y)**2});
 edges.sort((a,b)=>a.d-b.d||a.i-b.i||a.j-b.j);
 let count=0;
 for(const {i,j} of edges){
  if(links[i].length>=(i===si||i===ei?1:2)||links[j].length>=(j===si||j===ei?1:2))continue;
  const a=root(i),b=root(j);if(a===b)continue;
  // Joining the two reserved symmetry ends too soon would strand other points.
  if(si>=0&&ei>=0&&sizes[a]+sizes[b]<n){const s=root(si),e=root(ei);if((s===a||s===b)&&(e===a||e===b))continue}
  links[i].push(j);links[j].push(i);roots[b]=a;sizes[a]+=sizes[b];if(++count===n-1)break;
 }
 const first=si>=0?si:links.findIndex(list=>list.length===1),path=[];
 let previous=-1,current=first;
 while(current!==undefined&&current>=0){path.push(ps[current]);const next=links[current].find(i=>i!==previous);previous=current;current=next}
 // Uncross only intersecting segments. Do not replace nearby edges merely to
 // optimize a route from a prescribed first vertex.
 for(let pass=0;pass<n;pass++){let changed=false;for(let i=1;i<path.length-2;i++)for(let j=i+1;j<path.length-1;j++){
  const a=path[i-1],b=path[i],c=path[j],d=path[j+1];
  if(cross(a,b,c)*cross(a,b,d)<0&&cross(c,d,a)*cross(c,d,b)<0){path.splice(i,j-i+1,...path.slice(i,j+1).reverse());changed=true}
 }if(!changed)break}return path;
}
export function vertexName(index){const letters='ㄱㄴㄷㄹㅁㅂㅅㅇㅈㅊㅋㅌㅍㅎ';return letters[index%letters.length]+(index<letters.length?'':Math.floor(index/letters.length)+1)}
export function joinBoundary(path,mode,axis,center){const mirror=path.map(p=>mode==='line'?reflect(p,axis):opposite(p,center));return {mirror,outline:path.concat(mode==='line'?mirror.slice(1,-1).reverse():mirror.slice(1,-1))}}
export function contains(poly,p){if(poly.some((a,i)=>between(a,poly[(i+1)%poly.length],p)))return false;let yes=false;for(let i=0,j=poly.length-1;i<poly.length;j=i++){const a=poly[i],b=poly[j];if((a.y>p.y)!==(b.y>p.y)&&p.x<(b.x-a.x)*(p.y-a.y)/(b.y-a.y)+a.x)yes=!yes}return yes}
export function prepare(points,mode,axis,center){
 const ps=points.slice().sort(compare),preview=nearestPath(ps),fail=error=>({path:preview,mirror:[],outline:[],error});
 if(ps.length<3)return fail('점이 3개 이상 필요해요.');
 if(ps.some((p,i)=>!inside(p)||!Number.isInteger(p.x)||!Number.isInteger(p.y)||ps.slice(0,i).some(q=>same(p,q))))return fail('서로 다른 모눈 교점을 선택해 주세요.');
 const map=p=>mode==='line'?reflect(p,axis):opposite(p,center);if(!ps.map(map).every(inside))return fail('완성될 도형이 모눈 밖으로 나가요.');
 let pairs=[];
 if(mode==='line'){
  const sides=ps.map(p=>cross(axis[0],axis[1],p));if(sides.some(v=>v>1e-7)&&sides.some(v=>v< -1e-7))return fail('대칭축 한쪽에 점을 찍어 주세요.');
  const ends=ps.filter(p=>same(p,map(p)));if(ends.length!==2)return fail('대칭축 위에 양 끝점 2개를 찍어 주세요.');pairs=[[ends[0],ends[1]]];
 }else{
  if(ps.some(p=>same(p,center)))return fail('대칭의 중심에는 꼭짓점을 찍을 수 없어요.');
  ps.forEach((p,i)=>{const q=ps.slice(i+1).find(q=>same(q,map(p)));if(q)pairs.push([p,q])});
  if(!pairs.length)return fail('중심의 양쪽에 서로 대응하는 끝점 2개가 필요해요.');
 }
 const candidates=[];
 for(const [start,end] of pairs){
  const path=nearestPath(ps,start,end),{mirror,outline}=joinBoundary(path,mode,axis,center);
  if(area(outline)>1e-7&&simple(outline)&&(mode==='line'||contains(outline,center)))candidates.push({path,mirror,outline,error:null});
 }
 if(!candidates.length)return fail('선분이 겹치지 않도록 점의 위치를 바꿔 주세요.');
 candidates.sort((a,b)=>length(a.path)-length(b.path)||a.path.map(p=>`${p.y},${p.x}`).join(';').localeCompare(b.path.map(p=>`${p.y},${p.x}`).join(';')));
 return candidates[0];
}
export function validate(ps,mode,axis,center){return prepare(ps,mode,axis,center).error}
// Each guide traverses BOTH radii before the next letter begins.
export function guideSequence(path,mode,axis,center){const sorted=path.slice();if(mode==='point')return sorted;return sorted.filter(p=>!same(p,reflect(p,axis)))}
export function pageTurn(p,axis,t){const r=reflect(p,axis),q={x:(p.x+r.x)/2,y:(p.y+r.y)/2},v={x:p.x-q.x,y:p.y-q.y},d=Math.hypot(v.x,v.y);if(d<1e-8)return p;const [a,b]=axis,len=Math.hypot(b.x-a.x,b.y-a.y),u={x:(b.x-a.x)/len,y:(b.y-a.y)/len},angle=Math.PI*t-.22*Math.sin(Math.PI*t)*Math.min(1,d/6),z=d*Math.sin(angle),perspective=42/(42-z),anchor={x:(a.x+b.x)/2,y:(a.y+b.y)/2};return {x:anchor.x+(q.x-anchor.x+v.x*Math.cos(angle)+u.x*.12*z)*perspective,y:anchor.y+(q.y-anchor.y+v.y*Math.cos(angle)+u.y*.12*z)*perspective}}
export function timeline(ms,mode,reduced=false,guideCount=1){const lead=mode==='point'?guideCount*1600:0,move=mode==='point'?1600:2200,finish=lead+move;if(ms<lead)return {phase:'guides',progress:ms/lead,guides:true};if(ms<lead+move)return {phase:'move',progress:(ms-lead)/move,guides:mode==='point'};if(ms<finish+3000)return {phase:'blink',progress:1,guides:Math.floor((ms-finish)/500)%2===0};return {phase:'done',progress:1,guides:false}}

// Orient the existing nearest-edge chain; never alphabetize vertices by screen height.
export function referenceOrigin(points,mode,axis,center){if(mode==='point'||!points.length)return center;const mean={x:points.reduce((s,p)=>s+p.x,0)/points.length,y:points.reduce((s,p)=>s+p.y,0)/points.length},r=reflect(mean,axis);return {x:(mean.x+r.x)/2,y:(mean.y+r.y)/2}}
export function initialDirection(points,mode,axis,center){if(mode==='line'){for(let i=2;i<points.length;i++){const v=cross(points[0],points[i-1],points[i]);if(Math.abs(v)>1e-7)return Math.sign(v)}return null}for(let i=1;i<points.length;i++){const v=cross(center,points[i-1],points[i]);if(Math.abs(v)>1e-7)return Math.sign(v)}return null}
export function orientPath(path,points,mode,axis,center,direction){if(path.length<2)return path;const o=referenceOrigin(points,mode,axis,center),turn=path.slice(1).reduce((s,p,i)=>s+cross(o,path[i],p),0);if(direction&&Math.abs(turn)>1e-7)return Math.sign(turn)===direction?path:path.slice().reverse();const distanceToReference=p=>mode==='point'?distance(p,center):distance(p,reflect(p,axis))/2,a=path[0],b=path.at(-1),delta=distanceToReference(a)-distanceToReference(b);if(Math.abs(delta)>1e-7)return delta<0?path:path.slice().reverse();return points.findIndex(p=>same(p,a))<=points.findIndex(p=>same(p,b))?path:path.slice().reverse()}
