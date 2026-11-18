// SKAT Vision 6.70 (game workbench). Offline matching, review, editable fictional map, encrypted drafts.
// This module intentionally does NOT convert game grid coordinates to WGS84 / SK-42.
(() => {
'use strict';
if (window.__mod_vi) return;
window.__mod_vi = 1;
const V = {projectId:null,samples:[],custom:[],customLoaded:false,sampleLoaded:false,underlay:null,draggingMap:false,img:null, imageURL:null, src:null, w:0, h:0, regions:[], pick:0,
        mode:'select', grid:[], transform:null, reverse:null, status:'', scene:null,
        view:null, opacity:0.65, next:1, features:[], trace:[], imageDataUrl:null, projectName:'Новая игровая карта', latestSave:0, draftError:false, editDrag:null};
let root, cvs, ctx, scene, sceneCtx, fileInput, projectInput, prevCanvas;
const $v = id => root && root.querySelector('#'+id);
const esc = s => String(s??'').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const clamp=(x,a,b)=>Math.max(a,Math.min(b,x));
const GENERIC = [
  {id:'@building',n:'Здание / строение'}, {id:'@road',n:'Дорога / путь'},
  {id:'@bridge',n:'Мост / переход'}, {id:'@tree',n:'Дерево / растительность'},
  {id:'@vehicle',n:'Транспорт'}, {id:'@water',n:'Водоём'},
  {id:'@object',n:'Другой игровой объект'}
];
const syms=()=>SYMS.filter(s=>s.type==='pt' && ((s.d||[]).length || (s.f||[]).length || s.img));
const symOf=id=>SYM_BY[id]||GENERIC.find(s=>s.id===id)||V.custom.find(s=>s.id===id);
const symName=id=>(symOf(id)||{}).n||'Без обозначения';
const projectId=()=> 'g'+Date.now().toString(36)+Math.random().toString(36).slice(2,9);
const validPoint=p=>Array.isArray(p)&&p.length===2&&p.every(x=>typeof x==='number'&&Number.isFinite(x));
// Compact learned template: 32×32 monochrome mask packed into 128 bytes.
function packMask(m){const d=new Uint8Array(128);for(let i=0;i<1024;i++)if(m[i])d[i>>3]|=1<<(i&7);return btoa(String.fromCharCode(...d));}
function unpackMask(b){try{const a=atob(b);if(a.length!==128)return null;const m=new Uint8Array(1024);for(let i=0;i<1024;i++)m[i]=(+!!(a.charCodeAt(i>>3)&(1<<(i&7))));return m;}catch(e){return null;}}

const customImages=new Map();
function drawGameSymbol(g,id,x,y,color='#5aa2ff',angle=0){
  if(id?.startsWith('!')){
    const def=V.custom.find(s=>s.id===id);
    if(def){let im=customImages.get(id);
      if(!im){im=new Image();im.onload=()=>{if(scene)renderScene();};im.src=def.img;customImages.set(id,im);}
      if(im.complete&&im.naturalWidth){g.save();g.translate(x,y);g.rotate(angle);g.drawImage(im,-16,-16,32,32);g.restore();return;}
    }
  }
  if(id&&!id.startsWith('@')&&!id.startsWith('!')){drawSym(g,id,x,y,color,null,angle);return;}
  g.save();g.translate(x,y);g.rotate(angle);g.strokeStyle=color;g.fillStyle=color;g.lineWidth=2.4;
  if(id==='@road'){g.beginPath();g.moveTo(-16,-6);g.lineTo(16,-6);g.moveTo(-16,6);g.lineTo(16,6);g.stroke();}
  else if(id==='@building'){g.strokeRect(-12,-10,24,20);g.fillRect(-5,-5,10,10);}
  else if(id==='@bridge'){g.beginPath();g.moveTo(-16,-9);g.lineTo(16,-9);g.moveTo(-16,9);g.lineTo(16,9);g.moveTo(-8,-14);g.lineTo(-8,14);g.moveTo(8,-14);g.lineTo(8,14);g.stroke();}
  else if(id==='@tree'){g.beginPath();g.moveTo(0,-14);g.lineTo(-13,10);g.lineTo(13,10);g.closePath();g.stroke();g.beginPath();g.moveTo(0,10);g.lineTo(0,17);g.stroke();}
  else if(id==='@vehicle'){g.strokeRect(-14,-8,28,16);g.fillRect(-9,-12,6,4);g.fillRect(5,-12,6,4);g.fillRect(-9,8,6,4);g.fillRect(5,8,6,4);}
  else if(id==='@water'){g.beginPath();g.ellipse(0,0,14,9,0,0,2*Math.PI);g.stroke();}
  else {g.beginPath();g.arc(0,0,12,0,Math.PI*2);g.stroke();g.beginPath();g.moveTo(-17,0);g.lineTo(17,0);g.moveTo(0,-17);g.lineTo(0,17);g.stroke();}
  g.restore();
}

const bitmapMask = (pixels, w, h, mode) => {
  const out=new Uint8Array(w*h);
  for(let i=0,j=0;i<out.length;i++,j+=4){
    const r=pixels[j],g=pixels[j+1],b=pixels[j+2], hi=Math.max(r,g,b),lo=Math.min(r,g,b), sat=(hi-lo)/Math.max(1,hi);
    out[i]=(mode==='ink') ? (hi<110 ? 1:0) : (mode==='light') ? (lo>155?1:0) : (sat>.30 && hi>72 && hi-lo>36 ? 1:0);
  }
  return out;
};
function dilate(mask,w,h,r){
  const m=new Uint8Array(mask.length), d=new Uint8Array(mask.length);
  for(let y=0;y<h;y++)for(let x=0;x<w;x++){let any=0;for(let k=-r;k<=r;k++){const q=x+k;if(q>=0&&q<w&&mask[y*w+q]){any=1;break;}}m[y*w+x]=any;}
  for(let y=0;y<h;y++)for(let x=0;x<w;x++){let any=0;for(let k=-r;k<=r;k++){const q=y+k;if(q>=0&&q<h&&m[q*w+x]){any=1;break;}}d[y*w+x]=any;}
  return d;
}
function components(mask,w,h){
  const done=new Uint8Array(w*h), stack=new Int32Array(w*h), out=[];
  for(let at=0;at<mask.length;at++){
    if(!mask[at] || done[at]) continue;
    let top=0;stack[top++]=at;done[at]=1;let minx=w,miny=h,maxx=0,maxy=0,count=0;
    while(top){const q=stack[--top],y=(q/w)|0,x=q-y*w;count++;minx=Math.min(minx,x);maxx=Math.max(maxx,x);miny=Math.min(miny,y);maxy=Math.max(maxy,y);
      if(x>0 && mask[q-1] && !done[q-1]){done[q-1]=1;stack[top++]=q-1;}
      if(x+1<w && mask[q+1] && !done[q+1]){done[q+1]=1;stack[top++]=q+1;}
      if(y>0 && mask[q-w] && !done[q-w]){done[q-w]=1;stack[top++]=q-w;}
      if(y+1<h && mask[q+w] && !done[q+w]){done[q+w]=1;stack[top++]=q+w;}
    }
    out.push({x:minx,y:miny,w:maxx-minx+1,h:maxy-miny+1,count});
  }
  return out;
}
function normalized(mask, W, H, box, N=32){
  const out=new Uint8Array(N*N), x0=box.x,y0=box.y,w=box.w,h=box.h;
  const scale=(N-4)/Math.max(w,h), nw=w*scale,nh=h*scale,dx=(N-nw)/2,dy=(N-nh)/2;
  for(let y=0;y<N;y++)for(let x=0;x<N;x++){
    const u=(x+.5-dx)/scale, v=(y+.5-dy)/scale;
    if(u>=0&&u<w&&v>=0&&v<h){const px=clamp(Math.floor(x0+u),0,W-1),py=clamp(Math.floor(y0+v),0,H-1);out[y*N+x]=mask[py*W+px];}
  }
  return out;
}
function tighten(mask,w,h,box){
  let ax=w,ay=h,bx=-1,by=-1;
  for(let y=box.y;y<box.y+box.h;y++)for(let x=box.x;x<box.x+box.w;x++){
    if(x>=0&&x<w&&y>=0&&y<h&&mask[y*w+x]){ax=Math.min(ax,x);ay=Math.min(ay,y);bx=Math.max(bx,x);by=Math.max(by,y);}
  }
  return bx>=ax?{x:ax,y:ay,w:bx-ax+1,h:by-ay+1}:box;
}
function distances(mask,N=32){
  const out=new Uint8Array(N*N);out.fill(50);
  for(let y=0;y<N;y++)for(let x=0;x<N;x++)if(mask[y*N+x])out[y*N+x]=0;
  for(let y=0;y<N;y++)for(let x=0;x<N;x++){
    const i=y*N+x;if(x)out[i]=Math.min(out[i],out[i-1]+3);if(y)out[i]=Math.min(out[i],out[i-N]+3);if(x&&y)out[i]=Math.min(out[i],out[i-N-1]+4);
  }
  for(let y=N-1;y>=0;y--)for(let x=N-1;x>=0;x--){
    const i=y*N+x;if(x<N-1)out[i]=Math.min(out[i],out[i+1]+3);if(y<N-1)out[i]=Math.min(out[i],out[i+N]+3);if(x<N-1&&y<N-1)out[i]=Math.min(out[i],out[i+N+1]+4);
  }
  return out;
}
function signature(mask){let area=0;for(let x of mask)area+=x;return {mask,dist:distances(mask),area};}
function likeness(a,b){
  if(!a.area||!b.area) return 0;
  let ab=0,ba=0,hit=0;
  for(let i=0;i<a.mask.length;i++){if(a.mask[i]){ab+=Math.min(15,b.dist[i]);if(b.mask[i])hit++;}if(b.mask[i])ba+=Math.min(15,a.dist[i]);}
  const chamfer=1-(ab/Math.max(1,a.area)+ba/Math.max(1,b.area))/30;
  const dice=2*hit/(a.area+b.area);
  return clamp(.68*chamfer+.32*dice,0,1);
}
let templates=null;
function refSignatures(){
  if(templates)return templates;
  templates=[];
  const c=document.createElement('canvas');c.width=c.height=128;
  const g=c.getContext('2d',{willReadFrequently:true});
  for(const sym of syms()){
    if(sym.img)continue;
    for(const ang of [0,Math.PI/2,Math.PI,Math.PI*1.5]){
      g.clearRect(0,0,128,128);g.save();g.translate(64,64);g.rotate(ang);g.scale(4,4);
      try{drawSym(g,sym.id,0,0,'#1155dd');}catch(e){g.restore();continue;}
      g.restore();const ma=bitmapMask(g.getImageData(0,0,128,128).data,128,128,'color');
      const box=tighten(ma,128,128,{x:0,y:0,w:128,h:128});
      if(box.w<4||box.h<4)continue;
      templates.push({id:sym.id,name:sym.n,sig:signature(normalized(ma,128,128,box)),ratio:box.w/box.h,angle:ang});
    }
  }
  return templates;
}
function matchRegion(r){
  if(!V.src)return;
  const z=V.src,x=clamp(Math.floor(r.x),0,V.w-1),y=clamp(Math.floor(r.y),0,V.h-1);
  const box=tighten(z.mask,V.w,V.h,{x,y,w:Math.min(V.w-x,Math.max(1,Math.ceil(r.w))),h:Math.min(V.h-y,Math.max(1,Math.ceil(r.h)))});
  const a=signature(normalized(z.mask,V.w,V.h,box)),ratio=box.w/Math.max(1,box.h);
  const learned=V.regions.filter(q=>q!==r&&q.confirmed&&q.id&&!q.id.startsWith('@')).map(q=>{
    const bx=tighten(z.mask,V.w,V.h,q);
    return {id:q.id,sig:signature(normalized(z.mask,V.w,V.h,bx)),ratio:bx.w/Math.max(1,bx.h),angle:q.angle||0};
  });
  const scores=new Map();
  const saved=V.samples.filter(t=>symOf(t.id)).map(t=>({id:t.id,ratio:t.ratio,angle:t.angle||0,sig:t.sig,trained:true}));
  for(const t of [...refSignatures(),...learned,...saved]){
    const aspect=Math.exp(-.26*Math.abs(Math.log(Math.max(.02,ratio)/Math.max(.02,t.ratio))));
    const score=Math.min(1,likeness(a,t.sig)*aspect+(t.trained?.035:0)),old=scores.get(t.id);
    if(!old||score>old.score)scores.set(t.id,{id:t.id,n:symName(t.id),score,angle:t.angle||0});
  }
  r.ranking=[...scores.values()].sort((a,b)=>b.score-a.score).slice(0,8);
  if(!r.id&&r.ranking[0]&&r.ranking[0].score>=.28){r.id=r.ranking[0].id;r.angle=r.ranking[0].angle;}
}
function scan(){
  if(!V.src)return;
  // Never discard confirmed or hand-drawn objects on an automatic rescan.
  const protectedRegions=V.regions.filter(r=>r.confirmed||r.manual);
  setInfo('Ищу цветные области…');
  const {mask,w,h}=V.src, radius=clamp(Math.round(Math.min(w,h)/145),2,5);
  const comps=components(dilate(mask,w,h,radius),w,h).filter(b=>b.w>=13&&b.h>=13&&b.count>=45&&b.w*b.h>=350&&b.w<.8*w&&b.h<.8*h);
  const reg=[];
  for(const b of comps){
    const t=tighten(mask,w,h,b),areaRatio=t.w/t.h;
    // Wide, very short color regions are usually printed labels, not point signs.
    if(areaRatio>3.2&&t.h<55) continue;
    const r={rid:V.next++,x:Math.max(0,t.x-3),y:Math.max(0,t.y-3),w:Math.min(w-t.x+3,t.w+6),h:Math.min(h-t.y+3,t.h+6),id:null,confirmed:false,angle:0,label:''};
    matchRegion(r);reg.push(r);
  }
  const remaining=reg.filter(r=>!protectedRegions.some(p=>{
    const ix=Math.max(0,Math.min(r.x+r.w,p.x+p.w)-Math.max(r.x,p.x));
    const iy=Math.max(0,Math.min(r.y+r.h,p.y+p.h)-Math.max(r.y,p.y));
    return ix*iy/Math.max(1,Math.min(r.w*r.h,p.w*p.h))>.45;
  }));
  V.regions=[...protectedRegions,...remaining.slice(0,Math.max(0,300-protectedRegions.length))];
  V.pick=0;draw();renderItems();showCandidate();queueSave();
  setInfo(`Найдено областей: ${V.regions.length}. Подтверждённые и созданные вручную сохранены.`);
}
function focusSource(){
  const r=V.regions[V.pick],pane=$v('viImageScroller');if(!r||!pane||!V.w)return;
  const z=+$v('viZoom').value/100, w=V.w*z,h=V.h*z;
  pane.scrollLeft=clamp((r.x+r.w/2)*z-pane.clientWidth/2,0,Math.max(0,w-pane.clientWidth));
  pane.scrollTop=clamp((r.y+r.h/2)*z-pane.clientHeight/2,0,Math.max(0,h-pane.clientHeight));
}
function focusReview(next){if(!V.regions.length)return;const n=V.regions.length;
  if(next){const st=(V.pick+1)%n;let found=-1;for(let j=0;j<n;j++){const i=(st+j)%n;if(!V.regions[i].confirmed){found=i;break;}}if(found<0){setInfo('Все найденные области проверены.');return;}V.pick=found;}
  draw();renderItems();showCandidate();focusSource();
  const b=$v('viItems')?.querySelector(`[data-i="${V.pick}"]`);b?.scrollIntoView({block:'nearest',behavior:'auto'});
}
function sourceThumb(r){const c=document.createElement('canvas');c.width=132;c.height=112;const g=c.getContext('2d');g.fillStyle='#07111b';g.fillRect(0,0,132,112);
  const pad=8,sw=Math.max(1,r.w),sh=Math.max(1,r.h),a=Math.min((132-pad*2)/sw,(112-pad*2)/sh);const w=sw*a,h=sh*a;
  g.imageSmoothingEnabled=true;g.drawImage(prevCanvas,r.x,r.y,sw,sh,(132-w)/2,(112-h)/2,w,h);return c.toDataURL('image/png');}
function learnRegion(r){if(!V.src||!r.id||r.id.startsWith('@'))return;
  const z=V.src,box=tighten(z.mask,V.w,V.h,r),mask=normalized(z.mask,V.w,V.h,box);
  const sample={id:r.id,ratio:box.w/Math.max(1,box.h),angle:r.angle||0,mask:packMask(mask),time:Date.now()};
  if(V.samples.some(t=>t.id===sample.id&&t.mask===sample.mask))return;
  V.samples.push({...sample,sig:signature(mask)});if(V.samples.length>300)V.samples.splice(0,V.samples.length-300);
  saveSamples().catch(e=>console.warn('Vision learn',e));
}
function setInfo(t){V.status=t;const x=$v('viMsg');if(x)x.textContent=t;}
async function loadImage(blob,after){
  const replacingExisting=!!V.src;
  if(!blob||!/^image\//.test(blob.type)){setInfo('Выберите PNG, JPEG или другое изображение.');return Promise.resolve(false);}
  // Finish the previous map's pending autosave before replacing the active image.
  if(replacingExisting){
    clearTimeout(saveTimer);
    try{await saveDraft();}catch(e){
      setInfo('Предыдущий проект не удалось сохранить: '+(e.message||e));
      return false;
    }
  }
  if(V.imageURL)URL.revokeObjectURL(V.imageURL);V.imageURL=URL.createObjectURL(blob);
  return new Promise(resolve=>{
  const im=new Image();im.onload=()=>{
    if(im.naturalWidth*im.naturalHeight>60000000){
      URL.revokeObjectURL(V.imageURL);V.imageURL=null;
      setInfo('Разрешение изображения слишком большое. Уменьшите его до 60 мегапикселей.');resolve(false);return;
    }
    V.img=im;const sc=Math.min(1,1600/Math.max(im.naturalWidth,im.naturalHeight));V.w=Math.max(1,Math.round(im.naturalWidth*sc));V.h=Math.max(1,Math.round(im.naturalHeight*sc));
    prevCanvas=document.createElement('canvas');prevCanvas.width=V.w;prevCanvas.height=V.h;
    const p=prevCanvas.getContext('2d',{willReadFrequently:true});p.drawImage(im,0,0,V.w,V.h);
    V.underlay=null;V.projectId=projectId();if(replacingExisting){V.projectName='Новая игровая карта';$v('viName').value=V.projectName;}V.imageDataUrl=prevCanvas.toDataURL('image/jpeg',.88);V.src={data:p.getImageData(0,0,V.w,V.h),w:V.w,h:V.h,mask:null};
    refreshMask();V.regions=[];V.features=[];V.trace=[];V.grid=[];V.transform=V.reverse=null;V.pick=0;V.view=null;V.origin=null;V.baseView=null;
    cvs.width=V.w;cvs.height=V.h;
    sceneCtx.clearRect(0,0,scene.width,scene.height);
    sceneCtx.fillStyle='#111b1b';sceneCtx.fillRect(0,0,scene.width,scene.height);
    $v('viSceneMsg').textContent='Сначала привяжите подложку к условной игровой сетке.';
    draw();renderItems();showCandidate();updateGrid();setInfo('Изображение загружено. Найдите объекты или обведите рамкой вручную.');if(typeof after==='function') after();else queueSave();renderFeatures();
    V.img=null;URL.revokeObjectURL(V.imageURL);V.imageURL=null;resolve(true);
  };
  im.onerror=()=>{if(V.imageURL)URL.revokeObjectURL(V.imageURL);V.imageURL=null;setInfo('Не удалось прочитать изображение.');resolve(false);};im.src=V.imageURL;
  });
}
function refreshMask(){if(!V.src)return;V.src.mask=bitmapMask(V.src.data.data,V.w,V.h,$v('viMask').value);}
function draw(){
  if(!V.src)return;
  ctx.clearRect(0,0,V.w,V.h);ctx.drawImage(prevCanvas,0,0);
  V.regions.forEach((r,i)=>{
    ctx.lineWidth=Math.max(2,V.w/470);ctx.strokeStyle=i===V.pick?'#ffdf44':r.confirmed?'#45e596':'#ff896a';ctx.setLineDash(i===V.pick?[]:[5,4]);ctx.strokeRect(r.x,r.y,r.w,r.h);ctx.setLineDash([]);
    ctx.fillStyle=ctx.strokeStyle;ctx.fillRect(r.x,Math.max(0,r.y-19),22,18);ctx.font='bold 13px sans-serif';ctx.fillStyle='#121819';ctx.fillText(String(i+1),r.x+4,Math.max(14,r.y-5));
  });
  V.features.forEach((f,i)=>{
    if(!f.points||f.points.length<2)return;
    ctx.beginPath();ctx.strokeStyle='#44c7ff';ctx.lineWidth=3;
    f.points.forEach(([x,y],k)=>k?ctx.lineTo(x,y):ctx.moveTo(x,y));
    if(f.kind==='poly'){ctx.closePath();ctx.fillStyle='rgba(68,199,255,.18)';ctx.fill();}
    ctx.stroke();ctx.fillStyle='#44c7ff';ctx.font='bold 13px system-ui';ctx.fillText(f.label||('Контур '+(i+1)),f.points[0][0]+5,f.points[0][1]-8);
  });
  if(V.trace.length){ctx.beginPath();ctx.strokeStyle='#fddf5a';ctx.setLineDash([5,5]);ctx.lineWidth=3;
    V.trace.forEach(([x,y],k)=>k?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.stroke();ctx.setLineDash([]);
    for(const [x,y] of V.trace){ctx.fillStyle='#ffdb55';ctx.beginPath();ctx.arc(x,y,5,0,2*Math.PI);ctx.fill();}
  }
  V.grid.forEach((p,i)=>{ctx.strokeStyle='#ffe863';ctx.lineWidth=3;ctx.beginPath();ctx.arc(p[0],p[1],7,0,Math.PI*2);ctx.stroke();ctx.font='bold 17px sans-serif';ctx.fillStyle='#ffe863';ctx.fillText(['1 · СЗ','2 · СВ','3 · ЮВ','4 · ЮЗ'][i],p[0]+9,p[1]-8);});
  if(V.grid.length>=2){ctx.strokeStyle='#ffe863';ctx.setLineDash([9,5]);ctx.beginPath();ctx.moveTo(...V.grid[0]);V.grid.slice(1).forEach(p=>ctx.lineTo(...p));if(V.grid.length===4)ctx.closePath();ctx.stroke();ctx.setLineDash([]);}
}
function renderItems(){
  const el=$v('viItems');if(!el)return;
  el.innerHTML=V.regions.map((r,i)=>`<button type="button" class="viItem ${V.pick===i?'sel':''}" data-i="${i}"><span>${i+1}</span><span>${esc(r.id?symName(r.id):'Не распознано')}</span><small>${r.confirmed?'✓ подтверждено':r.ranking&&r.ranking[0]?'≈ '+Math.round(r.ranking[0].score*100)+'%':'?'} </small></button>`).join('')||'<p class="viMuted">Объектов пока нет.</p>';
  el.querySelectorAll('[data-i]').forEach(b=>b.onclick=()=>{V.pick=+b.dataset.i;draw();renderItems();showCandidate();});
  $v('viCount').textContent=V.regions.filter(x=>x.confirmed&&x.id).length+' подтверждено / '+V.regions.length+' найдено';
}
function iconURL(id,size=48){const own=V.custom.find(s=>s.id===id);if(own)return own.img;const c=document.createElement('canvas');c.width=c.height=size;try{const g=c.getContext('2d');g.translate(size/2,size/2);g.scale(size/42,size/42);drawGameSymbol(g,id,0,0,'#205cff');}catch(e){}return c.toDataURL('image/png');}
function showCandidate(){
  const el=$v('viChoice');if(!el)return;const r=V.regions[V.pick];
  if(!r){el.innerHTML='<p class="viMuted">Выберите найденную область.</p>';return;}
  const opts=(r.ranking||[]).slice(0,4);
  el.innerHTML=`<div class="viTitle">Область №${V.pick+1} ${r.confirmed?'· подтверждена':''}</div>
  <div class="viComparison"><div><small>Фрагмент оригинала</small><img src="${sourceThumb(r)}" alt="Фрагмент загруженного изображения"></div><div><small>Выбранный эталон</small><img src="${r.id?iconURL(r.id,120):''}" alt="Знак из библиотеки"></div></div>
  <div class="viMatches">${opts.map(t=>`<button class="viMatch ${r.id===t.id?'picked':''}" data-s="${esc(t.id)}"><img alt="" src="${iconURL(t.id)}"><span>${esc(t.n)}</span><small>${Math.round(t.score*100)}% сходство</small></button>`).join('')}</div>
  <div class="viFields"><input type="search" id="viSearch" placeholder="Поиск по библиотеке" autocomplete="off"><select id="viSelect" aria-label="Выберите знак"></select></div><div class="viActions"><button id="viCreateSymbol">＋ Создать знак из этого фрагмента</button></div>
  <label class="viFld">Игровая подпись <input id="viLabel" maxlength="80" value="${esc(r.label||'')}" placeholder="Необязательно"></label>
  <label class="viFld">Поворот <input type="range" id="viAngle" min="0" max="355" step="5" value="${Math.round((r.angle||0)*180/Math.PI)%360}"><output id="viAngleVal">${Math.round((r.angle||0)*180/Math.PI)%360}°</output></label>
  <div class="viActions"><button id="viAccept" class="viPrimary">✓ Подтвердить</button><button id="viNext">Следующий непроверенный</button><button id="viUnaccept">Снять подтверждение</button><button id="viRemove">Удалить область</button></div><div class="viActions"><button id="viFocusSource">Показать на снимке</button><button id="viResetObj">Вернуть на исходную позицию</button></div>`;
  const change=id=>{r.id=id;r.confirmed=false;const top=(r.ranking||[]).find(x=>x.id===id);if(top)r.angle=top.angle||0;showCandidate();renderItems();draw();queueSave();};
  el.querySelectorAll('[data-s]').forEach(b=>b.onclick=()=>change(b.dataset.s));
  const search=$v('viSearch'),sel=$v('viSelect');
  function fill(q){const list=[...GENERIC,...V.custom,...syms()].filter(s=>!q||s.n.toLowerCase().includes(q.toLowerCase())||s.id.toLowerCase().includes(q.toLowerCase())).slice(0,260);
    sel.innerHTML='<option value="">Выберите соответствие</option>'+list.map(s=>`<option value="${esc(s.id)}" ${r.id===s.id?'selected':''}>${esc(s.n)}</option>`).join('');}
  fill('');search.oninput=()=>fill(search.value.trim());sel.onchange=()=>change(sel.value||null);
  $v('viCreateSymbol').onclick=()=>{
    const name=prompt('Название нового игрового обозначения:',r.label||'Новый знак');
    if(name===null)return;const n=String(name).trim().slice(0,80);if(!n){setInfo('Введите название нового знака.');return;}
    const ic=document.createElement('canvas');ic.width=ic.height=96;const gg=ic.getContext('2d'),sz=Math.min(84/Math.max(1,r.w),84/Math.max(1,r.h));
    // Keep the original visual appearance: a cropped thumbnail with transparent margins.
    gg.drawImage(prevCanvas,r.x,r.y,r.w,r.h,(96-r.w*sz)/2,(96-r.h*sz)/2,r.w*sz,r.h*sz);
    const id='!'+Date.now().toString(36)+Math.random().toString(36).slice(2,6);
    V.custom.push({id,n,img:ic.toDataURL('image/png')});r.id=id;r.confirmed=false;
    saveCustoms().catch(e=>console.warn('Vision custom',e));
    showCandidate();renderItems();draw();queueSave();setInfo('Новый тип сохранён в локальном игровом каталоге. Подтвердите сопоставление.');
  };
  $v('viLabel').oninput=e=>{r.label=e.target.value;renderScene();queueSave();};
  $v('viAngle').oninput=e=>{r.angle=(+e.target.value)*Math.PI/180;$v('viAngleVal').textContent=e.target.value+'°';renderScene();queueSave();};
  $v('viNext').onclick=()=>focusReview(true);
  $v('viAccept').onclick=()=>{if(!symOf(r.id)){setInfo('Сначала выберите объект из библиотеки или общий игровой тип.');return;}r.confirmed=true;learnRegion(r);V.regions.filter(q=>!q.confirmed&&q!==r).forEach(q=>matchRegion(q));renderItems();showCandidate();draw();renderScene();queueSave();setInfo('Соответствие подтверждено. Похожие образцы обновлены.');};
  $v('viFocusSource').onclick=focusSource;
  $v('viResetObj').disabled=!r.overrideGame;
  $v('viResetObj').onclick=()=>{r.overrideGame=null;renderScene();showCandidate();queueSave();};
  $v('viUnaccept').onclick=()=>{r.confirmed=false;renderItems();showCandidate();draw();renderScene();queueSave();};
  $v('viRemove').onclick=()=>{V.regions.splice(V.pick,1);V.pick=clamp(V.pick,0,Math.max(0,V.regions.length-1));renderItems();showCandidate();draw();renderScene();queueSave();};
}
function normPointer(e,canvas){const r=canvas.getBoundingClientRect();return [clamp((e.clientX-r.left)*canvas.width/r.width,0,canvas.width),clamp((e.clientY-r.top)*canvas.height/r.height,0,canvas.height)];}
let down=null;
function boxHit(p,r,eps){
  const [x,y]=p,inside=x>=r.x-eps&&x<=r.x+r.w+eps&&y>=r.y-eps&&y<=r.y+r.h+eps;
  if(!inside)return null;
  const left=Math.abs(x-r.x)<eps,right=Math.abs(x-r.x-r.w)<eps,
    top=Math.abs(y-r.y)<eps,bottom=Math.abs(y-r.y-r.h)<eps;
  if((left||right)&&(top||bottom))return (top?'n':'s')+(left?'w':'e');
  return x>=r.x&&x<=r.x+r.w&&y>=r.y&&y<=r.y+r.h?'move':null;
}
function bindImageControls(){
  cvs.addEventListener('pointerdown',e=>{
    if(!V.src)return;const p=normPointer(e,cvs);down=p;
    if(V.mode==='rect'){cvs.setPointerCapture(e.pointerId);}
    else if(V.mode==='grid'){
      if(V.grid.length===4)V.grid=[];if(V.grid.length===0){V.transform=V.reverse=null;V.view=null;V.baseView=null;}
      V.grid.push(p);draw();updateGrid();queueSave();}
    else if(V.mode==='trace'){V.trace.push(p);draw();updateTraceInfo();}
    else if(V.mode==='edit'){
      const r=V.regions[V.pick],eps=clamp(V.w/90,9,28),hit=r?boxHit(p,r,eps):null;
      if(hit){V.editDrag={r,hit,start:p,box:{x:r.x,y:r.y,w:r.w,h:r.h},moved:false};cvs.setPointerCapture(e.pointerId);}
    }else{
      const indices=V.regions.map((r,i)=>({r,i})).filter(({r})=>p[0]>=r.x&&p[0]<=r.x+r.w&&p[1]>=r.y&&p[1]<=r.y+r.h)
        .sort((a,b)=>a.r.w*a.r.h-b.r.w*b.r.h);
      if(indices.length){V.pick=indices[0].i;draw();renderItems();showCandidate();}
    }
  });
  cvs.addEventListener('pointermove',e=>{
    if(!down||!V.src)return;
    const p=normPointer(e,cvs);
    if(V.mode==='edit'&&V.editDrag){
      const d=V.editDrag,b=d.box,dx=p[0]-d.start[0],dy=p[1]-d.start[1];
      if(Math.abs(dx)+Math.abs(dy)<1)return;
      const min=8;let x0=b.x,y0=b.y,x1=b.x+b.w,y1=b.y+b.h;
      if(d.hit==='move'){x0+=dx;x1+=dx;y0+=dy;y1+=dy;
        if(x0<0){x1-=x0;x0=0;}if(y0<0){y1-=y0;y0=0;}
        if(x1>V.w){x0-=x1-V.w;x1=V.w;}if(y1>V.h){y0-=y1-V.h;y1=V.h;}
      }else{
        if(d.hit.includes('w'))x0=clamp(b.x+dx,0,x1-min);
        if(d.hit.includes('e'))x1=clamp(b.x+b.w+dx,x0+min,V.w);
        if(d.hit.includes('n'))y0=clamp(b.y+dy,0,y1-min);
        if(d.hit.includes('s'))y1=clamp(b.y+b.h+dy,y0+min,V.h);
      }
      d.r.x=x0;d.r.y=y0;d.r.w=x1-x0;d.r.h=y1-y0;d.moved=true;draw();return;
    }
    if(V.mode==='rect'&&(e.buttons||e.pointerType==='touch')){
      draw();ctx.strokeStyle='#ffe863';ctx.lineWidth=3;
      ctx.strokeRect(down[0],down[1],p[0]-down[0],p[1]-down[1]);
    }
  });
  const end=e=>{
    if(!down)return;const a=down;down=null;
    if(V.editDrag){const d=V.editDrag;V.editDrag=null;
      if(d.moved){d.r.confirmed=false;d.r.overrideGame=null;d.r.ranking=[];d.r.id=null;
        matchRegion(d.r);draw();renderItems();showCandidate();renderScene();queueSave();
        setInfo('Рамка скорректирована, распознавание обновлено. Подтвердите знак повторно.');}
      return;
    }
    if(V.mode==='rect'&&V.src){const b=normPointer(e,cvs),x=clamp(Math.floor(Math.min(a[0],b[0])),0,V.w-1),y=clamp(Math.floor(Math.min(a[1],b[1])),0,V.h-1),w=Math.abs(b[0]-a[0]),h=Math.abs(b[1]-a[1]);if(w>12&&h>12){
        // User-created region absorbs unconfirmed fragments inside the same symbol.
        V.regions=V.regions.filter(o=>{
          if(o.confirmed)return true;
          const ix=Math.max(0,Math.min(x+w,o.x+o.w)-Math.max(x,o.x));
          const iy=Math.max(0,Math.min(y+h,o.y+o.h)-Math.max(y,o.y));
          return ix*iy/Math.max(1,o.w*o.h)<.72;
        });
        const r={rid:V.next++,x,y,w,h,id:null,confirmed:false,angle:0,label:'',manual:true};matchRegion(r);
        V.regions.push(r);V.pick=V.regions.length-1;renderItems();showCandidate();queueSave();}}draw();
  };
  cvs.addEventListener('pointerup',end);cvs.addEventListener('pointercancel',e=>{down=null;V.editDrag=null;draw();});
}
function solve8(M,y){
  M=M.map((r,i)=>[...r,y[i]]);
  for(let j=0;j<8;j++){
    let pivot=j;for(let k=j+1;k<8;k++)if(Math.abs(M[k][j])>Math.abs(M[pivot][j]))pivot=k;
    if(Math.abs(M[pivot][j])<1e-10)throw Error('Точки расположены некорректно.');
    [M[j],M[pivot]]=[M[pivot],M[j]];const d=M[j][j];for(let k=j;k<=8;k++)M[j][k]/=d;
    for(let r=0;r<8;r++)if(r!==j){const f=M[r][j];for(let k=j;k<=8;k++)M[r][k]-=f*M[j][k];}
  }
  return M.map(r=>r[8]);
}
function homography(src,dst){
  const a=[],b=[];
  for(let i=0;i<4;i++){
    const [x,y]=src[i],[u,v]=dst[i];a.push([x,y,1,0,0,0,-u*x,-u*y]);b.push(u);
    a.push([0,0,0,x,y,1,-v*x,-v*y]);b.push(v);
  }
  return [...solve8(a,b),1];
}
function warp(h,x,y){const z=h[6]*x+h[7]*y+h[8];return [(h[0]*x+h[1]*y+h[2])/z,(h[3]*x+h[4]*y+h[5])/z];}
function setMode(m){V.mode=m;root.querySelectorAll('.viMode').forEach(b=>b.classList.toggle('active',b.dataset.mode===m));
  setInfo(m==='rect'?'Протяните рамку вокруг обозначения.':m==='edit'?'Перемещайте выбранную рамку или тяните её углы. После изменения подтвердите знак заново.':m==='grid'?'Отметьте четыре угла одной клетки по порядку: СЗ, СВ, ЮВ, ЮЗ.':
    m==='trace'?'Касайтесь изображения, добавляя вершины линии или контура. Затем нажмите «Завершить».':'Коснитесь рамки, чтобы выбрать знак.');}
function updateTraceInfo(){const el=$v('viTraceCount');if(el)el.textContent=`Вершин: ${V.trace.length}`;}
function finishTrace(){
  const kind=$v('viTraceType').value;
  if(V.trace.length<(kind==='poly'?3:2)){setInfo('Для линии нужны 2 точки, для контура 3.');return;}
  const fid=V.next++,label=String($v('viTraceLabel').value||'').trim().slice(0,90);
  V.features.push({fid,kind,label,points:V.trace.map(q=>[...q])});V.trace=[];
  draw();updateTraceInfo();renderFeatures();renderScene();queueSave();
  setInfo('Линия или контур добавлен на отдельный игровой векторный слой.');
}
function renderFeatures(){const el=$v('viFeatureItems');if(!el)return;
  el.innerHTML=V.features.map((f,i)=>`<div class="viFeatRow"><span>${esc(f.label||('Фигура '+(i+1)))} · ${f.kind==='poly'?'контур':'линия'} · ${f.points.length} вершин</span><button data-f="${i}" type="button" aria-label="Удалить фигуру">✕</button></div>`).join('')||'<span class="viMuted">Линий и контуров нет.</span>';
  el.querySelectorAll('[data-f]').forEach(b=>b.onclick=()=>{
    V.features.splice(+b.dataset.f,1);renderFeatures();draw();renderScene();queueSave();});
}

function updateGrid(){const n=$v('viGridCount');if(n)n.textContent=`Контрольные точки: ${V.grid.length}/4`;}
function calibrate(){
  if(V.grid.length!==4){setInfo('Отметьте все четыре угла координатного квадрата.');return;}
  try{
    const X=Number($v('viX').value),Y=Number($v('viY').value),size=Number($v('viSize').value);
    if(!Number.isFinite(X)||!Number.isFinite(Y)||!Number.isFinite(size)||size<=0)throw Error('Некорректные координаты или размер клетки.');
    const dst=[[0,0],[1,0],[1,1],[0,1]];
    const cross=[];
    for(let i=0;i<4;i++){
      const a=V.grid[i],b=V.grid[(i+1)%4],c=V.grid[(i+2)%4];
      cross.push((b[0]-a[0])*(c[1]-b[1])-(b[1]-a[1])*(c[0]-b[0]));
    }
    if(cross.some(x=>Math.abs(x)<60)||!cross.every(x=>x>0)&&!cross.every(x=>x<0))
      throw Error('Четыре точки должны образовывать выпуклую клетку без пересечений.');
    V.transform=homography(V.grid,dst);V.reverse=homography(dst,V.grid);
    for(const p of V.grid){const z=warp(V.transform,...p);if(!z.every(Number.isFinite))throw Error('Неверная геометрия точек.');}
    V.origin={x:X,y:Y,size};V.view=null;V.baseView=null;V.underlay=null;
    setInfo('Подложка привязана к условной координатной сетке игрового сценария.');renderScene();queueSave();
  }catch(e){setInfo(e.message||String(e));}
}
function gameCoord(r){
  if(!V.transform||!V.origin)return null;
  const [u,v]=r.overrideGame?[r.overrideGame.u,r.overrideGame.v]:warp(V.transform,r.x+r.w/2,r.y+r.h/2);
  const step=V.origin.size/1000;const out={u,v,X:V.origin.x-v*step,Y:V.origin.y+u*step};return Object.values(out).every(Number.isFinite)?out:null;
}
function createScene(){if(!V.src||!V.transform)return;
  const b=[[0,0],[V.w,0],[V.w,V.h],[0,V.h]].map(p=>warp(V.transform,...p));
  let u0=Math.min(...b.map(p=>p[0])),u1=Math.max(...b.map(p=>p[0])),v0=Math.min(...b.map(p=>p[1])),v1=Math.max(...b.map(p=>p[1]));
  const pad=Math.max(.1,(u1-u0)*.05,(v1-v0)*.05);u0-=pad;u1+=pad;v0-=pad;v1+=pad;
  V.view={u0,u1,v0,v1};V.baseView={u0,u1,v0,v1};
}
function sceneProjection(){
  if(!V.view)return null;const box=V.view;
  const du=box.u1-box.u0,dv=box.v1-box.v0;
  if(!(du>0&&dv>0))return null;
  const k=Math.min(scene.width/du,scene.height/dv),ox=(scene.width-du*k)/2,oy=(scene.height-dv*k)/2;
  return {k,ox,oy,xy:(u,v)=>[ox+(u-box.u0)*k,oy+(v-box.v0)*k],uv:(x,y)=>[box.u0+(x-ox)/k,box.v0+(y-oy)/k]};
}
function gameZoom(f){
  if(!V.transform)return;if(!V.view)createScene();
  const a=V.view,b=V.baseView,cu=(a.u0+a.u1)/2,cv=(a.v0+a.v1)/2;
  const w=clamp((a.u1-a.u0)*f,(b.u1-b.u0)/12,(b.u1-b.u0)*8);
  const h=clamp((a.v1-a.v0)*f,(b.v1-b.v0)/12,(b.v1-b.v0)*8);
  V.view={u0:cu-w/2,u1:cu+w/2,v0:cv-h/2,v1:cv+h/2};renderScene();
}
let sceneRaf=0;
function scheduleScene(){if(sceneRaf)return;sceneRaf=requestAnimationFrame(()=>{sceneRaf=0;renderScene();});}
function sceneInput(){
  let drag=null,pinch=null;const touches=new Map();
  const point=e=>{const r=scene.getBoundingClientRect();return [(e.clientX-r.left)*scene.width/r.width,(e.clientY-r.top)*scene.height/r.height];};
  const two=()=>{const p=[...touches.values()];return {mid:[(p[0][0]+p[1][0])/2,(p[0][1]+p[1][1])/2],dist:Math.max(1,Math.hypot(p[0][0]-p[1][0],p[0][1]-p[1][1]))};};
  scene.addEventListener('pointerdown',e=>{
    if(!V.transform)return;if(!V.view)createScene();scene.setPointerCapture(e.pointerId);
    touches.set(e.pointerId,point(e));
    if(touches.size===2){const t=two(),P=sceneProjection();pinch={...t,view:{...V.view},anchor:P.uv(...t.mid)};drag=null;V.draggingMap=true;return;}
    if(touches.size>2)return;
    const [x,y]=point(e),P=sceneProjection();let best=null,dist=30;
    for(const r of V.regions){if(!r.confirmed||!r.id)continue;const p=gameCoord(r);if(!p)continue;
      const [px,py]=P.xy(p.u,p.v),d=Math.hypot(x-px,y-py);if(d<dist){dist=d;best=r;}}
    drag={p:[x,y],view:{...V.view},r:best,orig:best?gameCoord(best):null};
    V.draggingMap=!best;scene.style.cursor='grabbing';
    if(best){V.pick=V.regions.indexOf(best);renderItems();showCandidate();draw();}
  });
  scene.addEventListener('pointermove',e=>{
    if(!touches.has(e.pointerId))return;touches.set(e.pointerId,point(e));
    if(pinch&&touches.size>=2){const t=two(),orig=pinch.view,b=V.baseView;
      const ratio=clamp(pinch.dist/t.dist,.03,50),w=clamp((orig.u1-orig.u0)*ratio,(b.u1-b.u0)/12,(b.u1-b.u0)*8),h=clamp((orig.v1-orig.v0)*ratio,(b.v1-b.v0)/12,(b.v1-b.v0)*8);
      const k=Math.min(scene.width/w,scene.height/h),ox=(scene.width-w*k)/2,oy=(scene.height-h*k)/2;
      const u0=pinch.anchor[0]-(t.mid[0]-ox)/k,v0=pinch.anchor[1]-(t.mid[1]-oy)/k;
      V.view={u0,u1:u0+w,v0,v1:v0+h};scheduleScene();return;
    }
    if(!drag)return;const [x,y]=point(e),P=sceneProjection(),du=(x-drag.p[0])/P.k,dv=(y-drag.p[1])/P.k;
    if(drag.r){drag.r.overrideGame={u:drag.orig.u+du,v:drag.orig.v+dv};}
    else{const a=drag.view;V.view={u0:a.u0-du,u1:a.u1-du,v0:a.v0-dv,v1:a.v1-dv};}
    scheduleScene();
  });
  const finish=e=>{if(!touches.has(e.pointerId))return;
    const moved=!!(drag?.r);touches.delete(e.pointerId);
    if(touches.size<2)pinch=null;
    if(touches.size===0){drag=null;V.draggingMap=false;scene.style.cursor='grab';renderScene();if(moved){showCandidate();queueSave();}}
    else{drag=null;}
  };
  scene.addEventListener('pointerup',finish);scene.addEventListener('pointercancel',finish);
  scene.addEventListener('wheel',e=>{if(!V.transform)return;e.preventDefault();gameZoom(e.deltaY<0?.82:1.22);},{passive:false});
}

function renderScene(){
  if(!V.src||!V.transform)return;
  if(!V.view)createScene();
  const vw=scene.width,vh=scene.height,box=V.view;
  // Distinct coordinate axes: u increases east/right; v increases south/down.
  const du=box.u1-box.u0,dv=box.v1-box.v0;
  const k=Math.min(vw/du,vh/dv), U=(vw-du*k)/2,W=(vh-dv*k)/2;
  const loc=(u,v)=>[U+(u-box.u0)*k,W+(v-box.v0)*k];
  sceneCtx.fillStyle='#111b1b';sceneCtx.fillRect(0,0,vw,vh);
  if($v('viUnderlay').checked){
    const scale=V.draggingMap?.5:1,WW=Math.max(1,Math.round(vw*scale)),HH=Math.max(1,Math.round(vh*scale));
    const key=[V.w,V.h,box.u0,box.u1,box.v0,box.v1,V.opacity,WW,HH].join('|');
    if(!V.underlay||V.underlay.key!==key){
      const cv=document.createElement('canvas');cv.width=WW;cv.height=HH;
      const g=cv.getContext('2d'),out=g.createImageData(WW,HH),bits=out.data,base=V.src.data.data;
      const alpha=Math.round(255*V.opacity),sx=vw/WW,sy=vh/HH;
      // Cache the perspective-correct underlay; moving markers no longer resamples the image.
      for(let y=0;y<HH;y++)for(let x=0;x<WW;x++){
        const xx0=(x+.5)*sx,yy0=(y+.5)*sy;
        const [sx0,sy0]=warp(V.reverse,box.u0+(xx0-U)/k,box.v0+(yy0-W)/k);
        const xx=Math.floor(sx0),yy=Math.floor(sy0);
        if(xx>=0&&xx<V.w&&yy>=0&&yy<V.h){
          const q=(y*WW+x)*4,p=(yy*V.w+xx)*4;
          if(scale<1||xx+1>=V.w||yy+1>=V.h){bits[q]=base[p];bits[q+1]=base[p+1];bits[q+2]=base[p+2];}
          else{
            // Bilinear sampling on the settled view; fast nearest-neighbour while dragging.
            const fx=sx0-xx,fy=sy0-yy,fx0=1-fx,fy0=1-fy,p1=p+4,p2=p+V.w*4,p3=p2+4;
            for(let c=0;c<3;c++)bits[q+c]=Math.round(fy0*(fx0*base[p+c]+fx*base[p1+c])+fy*(fx0*base[p2+c]+fx*base[p3+c]));
          }
          bits[q+3]=alpha;
        }
      }
      g.putImageData(out,0,0);V.underlay={key,canvas:cv};
    }
    sceneCtx.drawImage(V.underlay.canvas,0,0,vw,vh);
  }

  sceneCtx.strokeStyle='rgba(255,227,91,.26)';sceneCtx.lineWidth=1;sceneCtx.fillStyle='#d5dba8';sceneCtx.font='12px sans-serif';
  const stepU=Math.max(1,Math.ceil((box.u1-box.u0)/14)),stepV=Math.max(1,Math.ceil((box.v1-box.v0)/14));
  for(let u=Math.ceil(box.u0/stepU)*stepU;u<=box.u1;u+=stepU){let x=loc(u,0)[0];sceneCtx.beginPath();sceneCtx.moveTo(x,0);sceneCtx.lineTo(x,vh);sceneCtx.stroke();sceneCtx.fillText('Y '+(V.origin.y+u*(V.origin.size/1000)).toFixed(2),x+3,14);}
  for(let v=Math.ceil(box.v0/stepV)*stepV;v<=box.v1;v+=stepV){let y=loc(0,v)[1];sceneCtx.beginPath();sceneCtx.moveTo(0,y);sceneCtx.lineTo(vw,y);sceneCtx.stroke();sceneCtx.fillText('X '+(V.origin.x-v*(V.origin.size/1000)).toFixed(2),3,y-5);}
  if($v('viFeatLayer')?.checked!==false)V.features.forEach(f=>{
    const pts=(f.points||[]).map(p=>warp(V.transform,...p)).filter(p=>p.every(Number.isFinite));if(pts.length<2)return;
    sceneCtx.beginPath();pts.forEach(([u,v],i)=>{const [x,y]=loc(u,v);i?sceneCtx.lineTo(x,y):sceneCtx.moveTo(x,y);});
    if(f.kind==='poly'){sceneCtx.closePath();sceneCtx.fillStyle='rgba(85,206,244,.23)';sceneCtx.fill();}
    sceneCtx.strokeStyle='#5ad8ff';sceneCtx.lineWidth=3;sceneCtx.stroke();
    if(f.label){const [x,y]=loc(...pts[0]);sceneCtx.fillStyle='#e3fbff';sceneCtx.font='bold 13px system-ui';sceneCtx.fillText(f.label,x+5,y-8);}
  });
  const confirmed=V.regions.filter(r=>r.confirmed&&r.id);
  confirmed.forEach(r=>{const p=gameCoord(r);if(!p)return;const [x,y]=loc(p.u,p.v);if(!Number.isFinite(x+y))return;
    sceneCtx.save();sceneCtx.fillStyle=r.overrideGame?'rgba(29,51,12,.85)':'rgba(6,17,30,.85)';sceneCtx.beginPath();sceneCtx.arc(x,y,24,0,Math.PI*2);sceneCtx.fill();
    try{drawGameSymbol(sceneCtx,r.id,x,y,'#3c83ff',r.angle||0);}catch(e){}if(r.label){sceneCtx.textAlign='center';sceneCtx.font='bold 13px system-ui';sceneCtx.lineWidth=3;sceneCtx.strokeStyle='#091522';sceneCtx.strokeText(r.label,x,y+36);sceneCtx.fillStyle='#ecf5ff';sceneCtx.fillText(r.label,x,y+36);}
    sceneCtx.restore();});
  $v('viSceneMsg').textContent=`Игровая сетка · ${confirmed.length} знаков · ${V.features.length} линий/контуров · шаг ${V.origin.size} игровых метров · без реальной геопривязки`;
}

// ===== MAIN MAP BRIDGE: generic non-military cartographic features only =====
// The Vision coordinate grid is fictional. This bridge places approved neutral
// features into the *visible bounds* of the main SKAT map for manual positioning.
// It does not interpret game X/Y as SK-42 and does not import tactical symbol IDs.
const NEUTRAL_TYPES = Object.freeze({
  '@building': '⌂', '@road': '═', '@bridge': '╫', '@tree': '♧', '@water': '≈'
});
function neutralPreview(){
  if(!V.src || !V.transform || !V.origin) return null;
  const candidates=V.regions.filter(r=>r.confirmed && Object.hasOwn(NEUTRAL_TYPES,r.id));
  if(!candidates.length)return {candidates:[],bounds:null,points:[]};
  const boundary=[[0,0],[V.w,0],[V.w,V.h],[0,V.h]].map(([x,y])=>warp(V.transform,x,y));
  const u0=Math.min(...boundary.map(p=>p[0])),u1=Math.max(...boundary.map(p=>p[0]));
  const v0=Math.min(...boundary.map(p=>p[1])),v1=Math.max(...boundary.map(p=>p[1]));
  if(!(u1-u0>1e-8&&v1-v0>1e-8))throw Error('Некорректная геометрия изображения.');
  const size=map.getSize();
  if(size.x<100||size.y<100)throw Error('Основная карта сейчас недоступна.');
  const points=candidates.map(r=>{
    const p=gameCoord(r);if(!p||!Number.isFinite(p.u)||!Number.isFinite(p.v))return null;
    const fx=(p.u-u0)/(u1-u0),fy=(p.v-v0)/(v1-v0);
    if(!Number.isFinite(fx)||!Number.isFinite(fy)||Math.abs(fx)>100||Math.abs(fy)>100)return null;
    // Fit to an inset rectangle. No assertion of exact geographical placement.
    const q=map.containerPointToLatLng(L.point(size.x*(.1+.8*fx),size.y*(.1+.8*fy)));
    if(!Number.isFinite(q.lat)||!Number.isFinite(q.lng)||Math.abs(q.lat)>85||Math.abs(q.lng)>180)return null;
    const label=String(r.label||symName(r.id)).slice(0,80);
    const glyph=NEUTRAL_TYPES[r.id];
    return {lat:q.lat,lng:q.lng,name:label,lbl:label,sym:'_none',visionKind:r.id,visionRid:r.rid,
      style:{color:'#3cc3e8',name:'Голубой',glyph},comment:'Игровая оцифровка Vision; положение на основной карте задано ориентировочно.'};
  }).filter(Boolean);
  return {candidates,bounds:{u0,u1,v0,v1},points};
}
function importNeutralMain(){
  try{
    if(window.SKAT_ED)throw Error('Сначала закройте проект Редактора, затем повторите импорт.');
    if(window.SEC?.meta && !window.SEC?.key)throw Error('Разблокируйте СКАТ перед переносом данных.');
    const p=neutralPreview();
    if(!p)throw Error('Сначала загрузите и привяжите игровое изображение четырьмя точками.');
    if(!p.points.length)throw Error('Нет подтверждённых нейтральных знаков. Допускаются здания, дороги, мосты, деревья и водоёмы.');
    const exists=state.arrays.find(a=>a.visionSource===V.projectId&&a.visionNeutral===true);
    const question=`Добавить ${p.points.length} нейтральных объектов в основной список слоёв СКАТ?\n\nПоложение будет ориентировочным, по текущему виду основной карты, а не по реальным координатам СК-42. Проверьте и переместите объекты вручную.\n\nСуществующие данные не удаляются.`;
    if(!confirm(question))return;
    const id=Date.now()+Math.floor(Math.random()*10000);
    const arr=normArr({id,kind:'pts',name:'Vision: '+String(V.projectName||'Игровая карта').slice(0,52),
      ident:'Vision · нейтральные объекты',style:{color:'#3cc3e8',name:'Голубой',glyph:''},
      points:p.points,shapes:[],texts:[],visionNeutral:true,visionSource:V.projectId,
      visionImportedAt:Date.now(),minZ:0,lblZ:10});
    if(exists){
      // Replace only a Vision-owned layer on explicit re-import; never mutate others.
      const idx=state.arrays.indexOf(exists);
      state.arrays.splice(idx,1,arr);
    }else state.arrays.push(arr);
    persistNow();renderMarkers();renderSheet();
    if(typeof renderLayers==='function' && document.getElementById('layModal')?.classList.contains('open'))renderLayers();
    root.classList.remove('viFocusGame');root.style.display='none';
    map.invalidateSize();
    toast(`Vision: ${p.points.length} нейтральных объектов на основной карте; координаты ориентировочные.`,5000);
  }catch(e){setInfo('Перенос не выполнен: '+(e.message||e));}
}

function projectData(){
  if(!V.src)return null;
  const name=V.projectName||'Новая игровая карта';
  return {format:'skat-vision-game',version:5,id:V.projectId||projectId(),name,updated:new Date().toISOString(),
    note:'Вымышленная игровая координатная система; географические координаты отсутствуют.',
    image:{width:V.w,height:V.h,data:V.imageDataUrl||prevCanvas.toDataURL('image/jpeg',.88)},
    customSymbols:V.custom.filter(c=>V.regions.some(r=>r.id===c.id)).map(c=>({id:c.id,n:c.n,img:c.img})),
    reference:V.transform?{corners:V.grid,origin:V.origin}:null,
    objects:V.regions.filter(r=>r.confirmed&&symOf(r.id)).map(r=>({
      symbolId:r.id,symbolName:symName(r.id),label:r.label||'',angle:r.angle||0,
      box:{x:r.x,y:r.y,w:r.w,h:r.h},game:gameCoord(r),overrideGame:r.overrideGame||null})),
    features:V.features.map(f=>({kind:f.kind,label:f.label,points:f.points,
      gamePoints:V.transform?f.points.map(pt=>{
        const [u,v]=warp(V.transform,...pt),step=V.origin.size/1000;
        return {X:V.origin.x-v*step,Y:V.origin.y+u*step};}):null})),
    review:V.regions.map(r=>({box:{x:r.x,y:r.y,w:r.w,h:r.h},symbolId:r.id,
      confirmed:!!r.confirmed,manual:!!r.manual,angle:r.angle||0,label:r.label||'',overrideGame:r.overrideGame||null}))};
}
function exportData(){
  const out=projectData();if(!out){setInfo('Сначала загрузите изображение.');return;}
  const blob=new Blob([JSON.stringify(out,null,2)],{type:'application/json'}),u=URL.createObjectURL(blob),a=document.createElement('a');
  a.href=u;a.download='SKAT-Vision-game.json';document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),12000);
  setInfo(`Экспортировано объектов: ${out.objects.length}. Файл не зашифрован PIN-кодом.`);
}
async function readProject(j){
  if(!V.customLoaded)await loadCustoms();
  if(j.format!=='skat-vision-game'||!j.image||typeof j.image.data!=='string'||!/^data:image\/(?:jpeg|png|webp);base64,/.test(j.image.data)) throw Error('Неверный формат проекта SKAT Vision.');
  if(j.image.data.length>22e6)throw Error('Превышен допустимый размер встроенного изображения.');
  const blob=await(await fetch(j.image.data)).blob();
  if(!await loadImage(blob,()=>{}))throw Error('Не удалось восстановить изображение.');
  V.imageDataUrl=j.image.data;
    V.projectId=typeof j.id==='string'&&/^g[a-z0-9]{5,30}$/.test(j.id)?j.id:projectId();
    V.projectName=String(j.name||'Восстановленный проект').slice(0,90);$v('viName').value=V.projectName;
    const incoming=(Array.isArray(j.customSymbols)?j.customSymbols:[]).slice(0,100).filter(c=>
      typeof c.id==='string'&&/^![a-z0-9]{5,30}$/i.test(c.id)&&typeof c.n==='string'&&typeof c.img==='string'&&c.img.length<150000&&/^data:image\/(?:png|jpeg|webp);base64,/.test(c.img));
    for(const c of incoming)if(!V.custom.some(o=>o.id===c.id))V.custom.push({id:c.id,n:c.n.slice(0,80),img:c.img});
    if(incoming.length)saveCustoms().catch(e=>console.warn('Vision custom',e));
    V.regions=(Array.isArray(j.review)?j.review:[]).slice(0,500).map(r=>{
      const x=clamp(Number(r.box?.x)||0,0,V.w-1),y=clamp(Number(r.box?.y)||0,0,V.h-1);
      return {rid:V.next++,x,y,w:clamp(Number(r.box?.w)||1,1,V.w-x),h:clamp(Number(r.box?.h)||1,1,V.h-y),
        id:typeof r.symbolId==='string'&&symOf(r.symbolId)?r.symbolId:null,
        confirmed:!!r.confirmed&&!!symOf(r.symbolId),manual:!!r.manual,
        angle:clamp(Number(r.angle)||0,0,2*Math.PI),
        label:String(r.label||'').slice(0,80),overrideGame:(r.overrideGame&&Number.isFinite(r.overrideGame.u)&&Number.isFinite(r.overrideGame.v))?{
          u:clamp(+r.overrideGame.u,-500,500),v:clamp(+r.overrideGame.v,-500,500)}:null,ranking:[]};});
    V.regions.forEach(r=>matchRegion(r));
    V.features=(Array.isArray(j.features)?j.features:[]).slice(0,300).map(f=>({fid:V.next++,kind:f.kind==='poly'?'poly':'line',
      label:String(f.label||'').slice(0,90),points:(Array.isArray(f.points)?f.points:[]).slice(0,1500).filter(p=>Array.isArray(p)&&p.length===2&&p.every(Number.isFinite))})).filter(f=>f.points.length>=(f.kind==='poly'?3:2));
    renderFeatures();V.grid=Array.isArray(j.reference?.corners)?j.reference.corners.slice(0,4).filter(p=>Array.isArray(p)&&p.length===2&&p.every(Number.isFinite)):[];
    if(j.reference?.origin){$v('viX').value=j.reference.origin.x;$v('viY').value=j.reference.origin.y;$v('viSize').value=j.reference.origin.size||1000;}
    if(j.reference?.origin){V.origin={x:Number(j.reference.origin.x),y:Number(j.reference.origin.y),size:Number(j.reference.origin.size)||1000};}
    V.underlay=null;
    V.pick=0;draw();renderItems();showCandidate();updateGrid();if(V.grid.length===4)calibrate();
    setInfo('Игровой проект восстановлен. Проверьте слои и подтверждённые объекты.');
}
async function importProject(file){
  try{
    if(!file||file.size>25e6)throw Error('Слишком большой файл проекта (максимум 25 МБ).');
    const j=JSON.parse(await file.text());await readProject(j);queueSave();
  }catch(e){setInfo('Не удалось открыть проект: '+(e.message||e));}
}
function exportCatalog(){
  const data={format:'skat-vision-catalog',version:1,customSymbols:V.custom.slice(-300).map(({id,n,img})=>({id,n,img})),
    samples:V.samples.slice(-300).map(({id,ratio,angle,mask,time})=>({id,ratio,angle,mask,time}))};
  const blob=new Blob([JSON.stringify(data,null,2)],{type:'application/json'}),u=URL.createObjectURL(blob),a=document.createElement('a');
  a.href=u;a.download='SKAT-Vision-catalog.json';document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),12000);
  setInfo(`Каталог экспортирован: ${data.customSymbols.length} собственных знаков, ${data.samples.length} образцов.`);
}
async function importCatalog(file){
  try{
    if(!file||file.size>25e6)throw Error('Каталог слишком большой.');
    const j=JSON.parse(await file.text());if(j.format!=='skat-vision-catalog'||j.version!==1)throw Error('Некорректный формат каталога.');
    const customs=(Array.isArray(j.customSymbols)?j.customSymbols:[]).slice(0,300).filter(c=>
      typeof c.id==='string'&&/^![a-z0-9]{5,30}$/i.test(c.id)&&typeof c.n==='string'&&typeof c.img==='string'&&c.img.length<150000&&/^data:image\/(?:png|jpeg|webp);base64,/.test(c.img));
    for(const c of customs)if(!V.custom.some(v=>v.id===c.id))V.custom.push({id:c.id,n:c.n.slice(0,80),img:c.img});
    V.custom=V.custom.slice(-300);await saveCustoms();
    const raw=(Array.isArray(j.samples)?j.samples:[]).slice(0,300);
    for(const q of raw){const mask=typeof q.mask==='string'?unpackMask(q.mask):null;
      if(!mask||!symOf(q.id)||!Number.isFinite(q.ratio)||q.ratio<=0||q.ratio>100||V.samples.some(t=>t.id===q.id&&t.mask===q.mask))continue;
      V.samples.push({id:q.id,ratio:q.ratio,angle:Number(q.angle)||0,mask:q.mask,time:Number(q.time)||Date.now(),sig:signature(mask)});
    }
    V.samples=V.samples.slice(-300);await saveSamples();
    V.sampleLoaded=V.customLoaded=true;
    $v('viLearned').textContent=`${V.samples.length} образцов и ${V.custom.length} своих знаков в каталоге.`;
    setInfo('Каталог успешно объединён с существующими образцами без удаления пользовательских знаков.');
  }catch(e){setInfo('Не удалось импортировать каталог: '+(e.message||e));}
}
let viDbp=null,saveTimer=0, saving=Promise.resolve();
function viDB(){if(viDbp)return viDbp;viDbp=new Promise((res,rej)=>{
  const rq=indexedDB.open('skat_vi',1);rq.onupgradeneeded=()=>{if(!rq.result.objectStoreNames.contains('projects'))rq.result.createObjectStore('projects');};
  rq.onsuccess=()=>res(rq.result);rq.onerror=()=>{viDbp=null;rej(rq.error);};
});return viDbp;}
async function viPut(record,key='latest',alias=false){const d=await viDB();return new Promise((res,rej)=>{const t=d.transaction('projects','readwrite'),st=t.objectStore('projects');
  st.put(record,key);if(alias)st.put({pointer:key,updated:record.updated,name:record.name,encrypted:record.encrypted},'latest');t.oncomplete=()=>res();t.onerror=t.onabort=()=>rej(t.error);});}
async function viDel(key){const d=await viDB();return new Promise((res,rej)=>{const t=d.transaction('projects','readwrite');t.objectStore('projects').delete(key);t.oncomplete=()=>res();t.onerror=t.onabort=()=>rej(t.error);});}
async function viKeys(){const d=await viDB();return new Promise((res,rej)=>{const t=d.transaction('projects','readonly'),q=t.objectStore('projects').getAllKeys();q.onsuccess=()=>res(q.result);q.onerror=()=>rej(q.error);});} 
async function viGet(key='latest'){const d=await viDB();return new Promise((res,rej)=>{const t=d.transaction('projects','readonly'),q=t.objectStore('projects').get(key);
  q.onsuccess=()=>res(q.result);q.onerror=()=>rej(q.error);});}
function queueSave(){if(!V.src)return;clearTimeout(saveTimer);saveTimer=setTimeout(()=>{saveDraft().catch(()=>{});},900);}
async function saveDraft(){if(!V.src)return;const project=projectData();if(!project)return;
  saving=saving.catch(()=>{}).then(async()=>{
    if(window.SEC?.meta&&!window.SEC?.key)throw Error('Потребуется разблокировать СКАТ для сохранения.');
    let payload=JSON.stringify(project),encrypted=false;
    if(window.SEC?.key){payload=await SEC.enc(new TextEncoder().encode(payload));encrypted=true;}
    await viPut({payload,encrypted,updated:Date.now(),name:project.name,id:project.id},'p:'+project.id,true);V.latestSave=Date.now();V.draftError=false;
    const x=$v('viAutosave');if(x)x.textContent='Черновик сохранён на устройстве'+(encrypted?' (шифрование)':'')+'.';
  });
  try{await saving;}catch(e){V.draftError=true;const x=$v('viAutosave');if(x)x.textContent='Автосохранение не удалось: '+(e.message||e);throw e;}
}
async function restoreDraft(key='latest'){
  try{let it=await viGet(key);if(it?.pointer)it=await viGet(it.pointer);if(!it){setInfo('Локальный черновик не найден.');return;}
    if(it.encrypted&&!window.SEC?.key)throw Error('Откройте СКАТ с PIN-кодом.');
    if(!it.encrypted&&window.SEC?.meta)throw Error('Черновик сохранён без PIN. Используйте экспорт JSON при смене режима шифрования.');
    const json=it.encrypted?new TextDecoder().decode(await SEC.dec(it.payload)):it.payload;
    await readProject(JSON.parse(json));setInfo('Черновик восстановлен с устройства.');
  }catch(e){setInfo('Не удалось восстановить черновик: '+(e.message||e));}
}

// User-defined symbolic types. Stored separately from the main SKAT library.
let customSaving=Promise.resolve();
async function saveCustoms(){
  const own=V.custom.slice(-300);customSaving=customSaving.catch(()=>{}).then(async()=>{
    if(window.SEC?.meta&&!window.SEC?.key)throw Error('СКАТ заблокирован');
    let payload=JSON.stringify(own),encrypted=false;
    if(window.SEC?.key){payload=await SEC.enc(new TextEncoder().encode(payload));encrypted=true;}
    await viPut({payload,encrypted,updated:Date.now()},'custom');
  });return customSaving;
}
async function loadCustoms(){try{
  const rec=await viGet('custom');if(!rec){V.customLoaded=true;return;}
  if(rec.encrypted&&!window.SEC?.key)return;if(!rec.encrypted&&window.SEC?.meta)return;
  const raw=rec.encrypted?new TextDecoder().decode(await SEC.dec(rec.payload)):rec.payload;
  const arr=JSON.parse(raw);V.custom=(Array.isArray(arr)?arr:[]).slice(-300).filter(c=>
    typeof c.id==='string'&&/^![a-z0-9]{5,30}$/i.test(c.id)&&typeof c.n==='string'&&typeof c.img==='string'&&c.img.length<150000&&/^data:image\/(?:png|jpeg|webp);base64,/.test(c.img));
  V.customLoaded=true;
}catch(e){console.warn('Vision custom catalog',e);}}
// Save only normalized silhouettes, never an uploaded image, as learning examples.
let sampleSaving=Promise.resolve();
async function saveSamples(){
  const own=V.samples.slice(-300).map(s=>({id:s.id,ratio:s.ratio,angle:s.angle,mask:s.mask,time:s.time}));
  sampleSaving=sampleSaving.catch(()=>{}).then(async()=>{
    if(window.SEC?.meta&&!window.SEC?.key)throw Error('СКАТ заблокирован');
    let payload=JSON.stringify(own),encrypted=false;
    if(window.SEC?.key){payload=await SEC.enc(new TextEncoder().encode(payload));encrypted=true;}
    await viPut({payload,encrypted,updated:Date.now()},'learned');
  });return sampleSaving;
}
async function loadSamples(){try{
  const rec=await viGet('learned');if(!rec)return;
  if(rec.encrypted&&!window.SEC?.key)return;
  if(!rec.encrypted&&window.SEC?.meta)return;
  const raw=rec.encrypted?new TextDecoder().decode(await SEC.dec(rec.payload)):rec.payload;
  const arr=JSON.parse(raw);V.samples=(Array.isArray(arr)?arr:[]).slice(-300).map(t=>{
    const mask=unpackMask(t.mask);return mask&&symOf(t.id)?{...t,sig:signature(mask)}:null;}).filter(Boolean);
  V.sampleLoaded=true;
  const m=$v('viLearned');if(m)m.textContent=V.samples.length+' эталонов сохранено на устройстве.';
}catch(e){console.warn('Vision training',e);}}
async function showProjects(){
  const pane=$v('viProjects');if(!pane)return;
  pane.hidden=false;pane.textContent='Читаю сохранённые карты…';
  try{
    const keys=(await viKeys()).filter(k=>typeof k==='string'&&k.startsWith('p:'));
    const entries=(await Promise.all(keys.map(async key=>({key,data:await viGet(key)})))).filter(x=>x.data);
    entries.sort((a,b)=>(b.data.updated||0)-(a.data.updated||0));
    pane.innerHTML='<div class="viPaneTitle">Сохранённые игровые карты</div>'+(entries.length?entries.slice(0,80).map(({key,data})=>`<div class="viFeatRow"><span><b>${esc(data.name||'Без названия')}</b><small> · ${new Date(data.updated).toLocaleString('ru-RU')} ${data.encrypted?' · 🔒':''}</small></span><div><button data-open="${esc(key)}">Открыть</button> <button data-del="${esc(key)}" aria-label="Удалить">✕</button></div></div>`).join(''):'<p class="viMuted">Пока нет сохранённых проектов; старый черновик можно открыть кнопкой «Черновик».</p>')+'<div class="viActions"><button id="viProjectsClose">Скрыть список</button></div>';
    pane.querySelector('#viProjectsClose').onclick=()=>{pane.hidden=true;};
    pane.querySelectorAll('[data-open]').forEach(b=>b.onclick=async()=>{await restoreDraft(b.dataset.open);pane.hidden=true;});
    pane.querySelectorAll('[data-del]').forEach(b=>b.onclick=async()=>{if(!confirm('Удалить этот сохранённый игровой проект? Экспорт JSON остаётся доступен, если сделана копия.'))return;
      try{const lt=await viGet('latest');await viDel(b.dataset.del);if(lt?.pointer===b.dataset.del)await viDel('latest');if(b.dataset.del==='p:'+V.projectId)V.projectId=projectId();await showProjects();setInfo('Проект удалён из локального списка.');}catch(e){setInfo('Ошибка удаления: '+(e.message||e));}});
  }catch(e){pane.textContent='Не удалось получить список: '+(e.message||e);}
}
function mount(){
  if(document.getElementById('viBox'))return;
  const st=document.createElement('style');st.id='viStyle';st.textContent=`
#viBox{position:fixed;inset:0;z-index:3600;background:#090f14;color:#dfe8f3;overflow-y:auto;font:14px/1.4 system-ui,-apple-system,sans-serif;overscroll-behavior:contain}
#viBox *{box-sizing:border-box}#viBox button,#viBox input,#viBox select{font:inherit}#viBox button{cursor:pointer;color:#e8f0ff;border:1px solid #3b4e61;border-radius:9px;background:#1b2938;padding:8px 10px}
#viBox button:active{opacity:.7}#viBox .viPrimary,#viBox .active{background:#18577d;border-color:#46b2ff;color:white}
#viBox header{position:sticky;top:0;z-index:5;padding:calc(env(safe-area-inset-top,0px) + 10px) 12px 10px;background:#101b27;border-bottom:1px solid #304153;display:flex;align-items:center;gap:10px}
#viBox header b{font-size:16px}#viBox header small{display:block;color:#97afc0}#viBox .viMain{display:grid;grid-template-columns:minmax(220px,1fr) minmax(245px,330px);gap:12px;padding:12px;max-width:1350px;margin:auto}
#viBox .viPanel{padding:12px;background:#111d29;border:1px solid #304054;border-radius:12px;min-width:0}
#viBox .viPaneTitle{font-weight:750;margin:0 0 8px;font-size:15px}
#viBox .viActions{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0}#viBox .viActions>*{flex:1;min-width:105px}
#viBox .viMode{font-size:12px}#viBox input:not([type=file]):not([type=checkbox]),#viBox select{background:#0e1722;color:#eff6ff;border:1px solid #465466;border-radius:8px;padding:8px;max-width:100%;min-width:0}
#viBox canvas{max-width:100%;height:auto;display:block;margin:auto;border-radius:8px;background:#070c15}#viImg{width:auto;touch-action:none;cursor:crosshair}
#viBox .viPreview{overflow:auto;max-height:62vh;min-height:120px;border:1px solid #34465a;border-radius:9px;background:#04090d;padding:5px}
#viBox .viMuted{color:#a6b5c5;font-size:12px}#viBox .viFields{display:grid;grid-template-columns:1fr 1fr;gap:6px}#viBox .viFields>*{width:100%}
#viBox .viGrid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:6px}#viBox label{display:block;font-size:12px;color:#c7d3df}#viBox label input{width:100%;margin-top:3px}
#viBox .viItems{max-height:180px;overflow-y:auto;display:flex;flex-direction:column;gap:4px}#viBox .viItem{display:grid;grid-template-columns:24px 1fr auto;align-items:center;text-align:left;gap:5px;padding:5px 7px;font-size:12px}#viBox .viItem small{opacity:.65}#viBox .viItem.sel{border-color:#f7df6e}
#viBox .viComparison{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:8px 0}#viBox .viComparison>div{background:#091522;border:1px solid #304356;border-radius:8px;padding:5px;text-align:center}#viBox .viComparison img{width:100%;height:108px;object-fit:contain;image-rendering:auto}#viBox .viComparison small{display:block;color:#adbdca;margin-bottom:3px}#viBox .viMatches{display:grid;grid-template-columns:1fr 1fr;gap:6px;margin:8px 0}#viBox .viMatch{min-width:0;display:flex;flex-wrap:wrap;align-items:center;gap:5px;font-size:11px;text-align:left}#viBox .viMatch img{width:38px;height:38px;object-fit:contain;background:#d9e3e7;border-radius:4px}#viBox .viMatch span{flex:1;min-width:70px}#viBox .viMatch small{display:block;color:#aaccdd}#viBox .viMatch.picked{border-color:#f6d753}
#viBox .viFeatRow{display:flex;justify-content:space-between;align-items:center;gap:8px;border-bottom:1px solid #324254;padding:4px 0}#viBox .viFld{display:flex;gap:7px;align-items:center;margin:7px 0}#viBox .viFld input{flex:1;min-width:0}#viBox .viTitle{font-weight:700}#viBox #viMsg{margin:0 12px 10px;color:#a9cfff;min-height:18px}
#viBox .viScene{padding:12px;max-width:1350px;margin:0 auto}#viBox #viGame{touch-action:none;cursor:grab}#viBox #viGame{border:1px solid #4b6074;width:100%;max-width:850px;height:auto;display:block;object-fit:contain}
#viBox .viImgHint{font-size:12px;color:#9ec7dd}
#viBox #viImg{touch-action:none}
#viBox.viFocusGame>.viScene{position:fixed;inset:0;z-index:20;display:flex;flex-direction:column;padding:calc(env(safe-area-inset-top,0px) + 8px) 10px calc(env(safe-area-inset-bottom,0px) + 10px);max-width:none;margin:0;border-radius:0}
#viBox.viFocusGame #viGame{flex:1;min-height:190px;max-width:none;width:100%;height:100%;object-fit:fill}
#viBox.viFocusGame .viScene .viBar{margin-top:5px}
#viBox.viFocusGame .viScene .viMuted{margin:3px 0}
#viBox .viBar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-top:10px}#viBox .viBar input[type=range]{width:115px}
@media(max-width:720px){#viBox .viMain{grid-template-columns:1fr;padding:8px}#viBox .viPreview{max-height:45vh}#viBox .viMatches{grid-template-columns:1fr 1fr}#viBox .viScene{padding:8px}}
`;document.head.appendChild(st);
  root=document.createElement('div');root.id='viBox';root.innerHTML=`
<header><div style="flex:1"><b>СКАТ VISION · игровая мастерская 6.70</b><small>Знаки СКАТ · ручное подтверждение · игровая сетка · черновики</small></div><button id="viClose" aria-label="Закрыть">✕</button></header>
<div class="viMain"><div class="viPanel">
  <div class="viPaneTitle">1. Исходное изображение</div>
  <label class="viFld">Название проекта <input id="viName" maxlength="90" value="Новая игровая карта"></label>
  <div class="viActions"><button id="viFileBtn" class="viPrimary">📷 Загрузить карту</button><button id="viDemo">Найти объекты</button><button id="viProjectBtn">Открыть JSON</button><button id="viRestore">Черновик</button><button id="viProjectsBtn">Мои карты</button></div><div id="viProjects" hidden></div><p id="viLearned" class="viMuted">Подтверждённые знаки можно запоминать как локальные образцы.</p>
  <input id="viFile" type="file" accept="image/*" hidden><input id="viProject" type="file" accept=".json,application/json" hidden><input id="viCatalogInput" type="file" accept=".json,application/json" hidden>
  <div class="viActions"><button id="viCatalogExport">Экспорт каталога</button><button id="viCatalogImport">Импорт каталога</button></div>
  <div class="viActions"><select id="viMask" aria-label="Тип пикселей"><option value="color">Цветные знаки</option><option value="ink">Тёмная графика на светлом</option><option value="light">Белые знаки на тёмном</option></select><button id="viScan">Пересканировать</button></div>
  <div class="viActions"><button class="viMode active" data-mode="select">Знаки</button><button class="viMode" data-mode="rect">Новая рамка</button><button class="viMode" data-mode="edit">Править рамку</button><button class="viMode" data-mode="trace">Контуры</button><button class="viMode" data-mode="grid">4 точки</button></div>
  <div class="viActions"><select id="viTraceType"><option value="line">Линия / дорога</option><option value="poly">Контур / площадной объект</option></select><input id="viTraceLabel" maxlength="90" placeholder="Название контура"></div>
  <div class="viActions"><button id="viTraceUndo">↶ Вершина</button><button id="viTraceDone" class="viPrimary">Завершить контур</button><small id="viTraceCount">Вершин: 0</small></div>
  <div id="viFeatureItems" class="viMuted"></div>
  <div class="viActions"><label>Увеличение изображения <input type="range" id="viZoom" min="100" max="400" step="25" value="100"></label><span id="viZoomV" class="viMuted">100%</span></div>
  <div class="viPreview" id="viImageScroller"><canvas id="viImg" width="500" height="280"></canvas></div><p class="viMuted">Жёлтая рамка: выбранный объект. Зелёная: подтверждённый. Красная: требуется проверка. Проценты показывают сходство формы, не вероятность правильного ответа.</p>
  </div><div class="viPanel"><div class="viPaneTitle">2. Сопоставление с библиотекой СКАТ</div>
  <div id="viCount" class="viMuted">0 объектов</div><div id="viItems" class="viItems"></div><div id="viChoice"></div>
  <hr style="border:0;border-top:1px solid #334b62;margin:12px 0"><div class="viPaneTitle">3. Игровая координатная сетка</div>
  <p class="viMuted" id="viGridCount">Контрольные точки: 0/4</p>
  <div class="viGrid"><label>X (верхняя граница)<input type="number" id="viX" value="5474"></label><label>Y (левая граница)<input type="number" id="viY" value="7426"></label><label>Сторона, игр. м<input type="number" id="viSize" value="1000" min="1"></label></div>
  <p class="viMuted">Точки по порядку: верхний левый → верхний правый → нижний правый → нижний левый угол клетки. X растёт к северу, Y к востоку. Значения условные, не GPS.</p>
  <div class="viActions"><button id="viGridUndo">↶ Убрать точку</button><button id="viClearGrid">Сбросить точки</button><button class="viPrimary" id="viCal">Привязать подложку</button></div></div></div>
<div class="viScene viPanel"><div class="viPaneTitle">4. Игровая карта · отдельный слой</div>
 <canvas id="viGame" width="850" height="570"></canvas><div id="viSceneMsg" class="viMuted">Сначала выберите четыре угла и выполните привязку.</div>
 <div class="viBar"><button id="viImportNeutral" class="viPrimary">В основной СКАТ: нейтральные объекты</button><button id="viFullscreen">⛶ Развернуть игровую карту</button><button id="viGamePlus">＋ Приблизить</button><button id="viGameMinus">－ Отдалить</button><button id="viGameReset">Вся карта</button></div>
 <p class="viMuted">Перенос в основную карту доступен только для нейтральных графических объектов. Он размещает их ориентировочно в текущем видимом участке карты СКАТ, не преобразуя игровые координаты в СК-42.</p>
 <p class="viMuted">Перетаскивайте карту для перемещения, колесо мыши или кнопки для масштаба. Для корректировки игрового положения перетащите знак; его рамка на исходном снимке сохранится.</p>
 <div class="viBar"><label><input type="checkbox" id="viUnderlay" checked> Подложка</label><label><input type="checkbox" id="viFeatLayer" checked> Контуры</label><label>Прозрачность <input type="range" id="viOpacity" min="0" max="100" value="65"></label><button id="viSave" class="viPrimary">Сохранить черновик</button><button id="viExport" class="viPrimary">Экспорт JSON</button><button id="viExportPng">Изображение PNG</button></div>
 <p class="viMuted" id="viAutosave">Локальный черновик доступен после загрузки изображения.</p></div>
<p id="viMsg" role="status"></p>`;
  document.body.appendChild(root);cvs=$v('viImg');ctx=cvs.getContext('2d');scene=$v('viGame');sceneCtx=scene.getContext('2d');
  fileInput=$v('viFile');projectInput=$v('viProject');$v('viFileBtn').onclick=()=>fileInput.click();fileInput.onchange=()=>{const f=fileInput.files[0];
    if(f&&f.size>30e6)setInfo('Изображение слишком большое: более 30 МБ. Сожмите его перед загрузкой.');
    else if(f)loadImage(f);
    fileInput.value='';};$v('viProjectBtn').onclick=()=>projectInput.click();projectInput.onchange=()=>{const f=projectInput.files[0];if(f)importProject(f);projectInput.value='';};
  $v('viCatalogExport').onclick=exportCatalog;
  $v('viCatalogImport').onclick=()=>$v('viCatalogInput').click();
  $v('viCatalogInput').onchange=e=>{const f=e.target.files[0];if(f)importCatalog(f);e.target.value='';};
  $v('viDemo').onclick=()=>{refreshMask();scan();};$v('viScan').onclick=()=>{refreshMask();scan();};$v('viMask').onchange=()=>{refreshMask();setInfo('Режим поиска изменён. Нажмите «Пересканировать».');};
  $v('viClose').onclick=()=>{if(V.src)saveDraft().catch(e=>console.warn('Vision close save',e));root.classList.remove('viFocusGame');root.style.display='none';};
  root.querySelectorAll('[data-mode]').forEach(b=>b.onclick=()=>setMode(b.dataset.mode));
  $v('viGridUndo').onclick=()=>{V.grid.pop();V.transform=V.reverse=null;V.view=V.baseView=null;V.underlay=null;draw();updateGrid();queueSave();};
  $v('viClearGrid').onclick=()=>{V.grid=[];V.transform=V.reverse=null;V.view=null;V.baseView=null;draw();updateGrid();queueSave();};
  $v('viCal').onclick=calibrate;
  $v('viImportNeutral').onclick=importNeutralMain;
  $v('viTraceUndo').onclick=()=>{V.trace.pop();updateTraceInfo();draw();};
  $v('viTraceDone').onclick=finishTrace;
  $v('viFullscreen').onclick=()=>{
    const active=root.classList.toggle('viFocusGame');$v('viFullscreen').textContent=active?'← Вернуться к редактору':'⛶ Развернуть игровую карту';
    requestAnimationFrame(()=>{if(active){const b=scene.getBoundingClientRect(),factor=Math.min(1,1400/Math.max(b.width,b.height));
      scene.width=Math.max(320,Math.round(b.width*factor));scene.height=Math.max(240,Math.round(b.height*factor));}
      else{scene.width=850;scene.height=570;}V.underlay=null;renderScene();});
  };
  $v('viGamePlus').onclick=()=>gameZoom(.8);
  $v('viGameMinus').onclick=()=>gameZoom(1.25);
  $v('viGameReset').onclick=()=>{if(V.baseView){V.view={...V.baseView};renderScene();}};
  $v('viFeatLayer').onchange=renderScene;
  $v('viSave').onclick=()=>saveDraft().then(()=>setInfo('Черновик сохранён.')).catch(e=>setInfo('Ошибка сохранения: '+e.message));
  $v('viRestore').onclick=()=>restoreDraft();$v('viProjectsBtn').onclick=showProjects;
  $v('viName').oninput=e=>{V.projectName=e.target.value.slice(0,90);queueSave();};
  $v('viZoom').oninput=e=>{const v=+e.target.value;$v('viZoomV').textContent=v+'%';
    cvs.style.width=(V.w||500)*(v/100)+'px';cvs.style.maxWidth='none';};
  $v('viExport').onclick=exportData;
  $v('viExportPng').onclick=()=>{if(!V.transform){setInfo('Сначала привяжите игровую карту.');return;}
    renderScene();scene.toBlob(blob=>{if(!blob){setInfo('Не удалось создать PNG.');return;}
      const u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download='SKAT-Vision-game.png';a.click();setTimeout(()=>URL.revokeObjectURL(u),10000);
      setInfo('Изображение игровой карты создано.');},'image/png');};
  $v('viUnderlay').onchange=renderScene;$v('viOpacity').oninput=e=>{V.opacity=(+e.target.value)/100;renderScene();};
  bindImageControls();sceneInput();
  ctx.fillStyle='#15212c';ctx.fillRect(0,0,500,280);ctx.fillStyle='#a8b8c6';ctx.font='17px sans-serif';ctx.fillText('Загрузите изображение',150,140);
  sceneCtx.fillStyle='#15212c';sceneCtx.fillRect(0,0,850,570);sceneCtx.fillStyle='#a8b8c6';sceneCtx.font='22px sans-serif';sceneCtx.fillText('Здесь появится игровая карта',255,270);
  renderItems();renderFeatures();showCandidate();setInfo('Готов к загрузке. Использую существующую библиотеку СКАТ и локальные вычисления.');
}
window.viOpen = () => {mount();root.style.display='block';if(!V.customLoaded)loadCustoms().then(()=>{if(!V.sampleLoaded)loadSamples();});else if(!V.sampleLoaded)loadSamples();};
})();
