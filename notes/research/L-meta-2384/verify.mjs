function verifyNestedCovers() {
  const edges = [[0,9],[0,10],[1,4],[1,8],[2,5],[2,10],[3,6],[3,7],[4,8],[4,10],[5,8],[5,9],[6,7],[6,10],[7,9],[8,9]];
  const vertexCount = 1 << 11;
  const edgeCount = 1 << edges.length;
  const size = new Uint8Array(vertexCount);
  const omitted = new Uint16Array(vertexCount);
  const inside = new Uint16Array(vertexCount);
  const covers = [];
  const independent = [];
  for (let vertices = 0; vertices < vertexCount; ++vertices) {
    size[vertices] = size[vertices >> 1] + (vertices & 1);
    for (const [i, [a, b]] of edges.entries()) {
      const pair = (1 << a) | (1 << b);
      if ((vertices & pair) === 0) omitted[vertices] |= 1 << i;
      if ((vertices & pair) === pair) inside[vertices] |= 1 << i;
    }
    if (omitted[vertices] === 0) covers.push(vertices);
    if (inside[vertices] === 0) independent.push(vertices);
  }
  const completion = new Uint8Array(vertexCount).fill(11);
  const best = new Uint16Array(edgeCount);
  for (let vertices = 0; vertices < vertexCount; ++vertices) {
    for (const cover of covers) {
      if ((vertices & cover) === vertices)
        completion[vertices] = Math.min(completion[vertices], size[cover]);
    }
    let retained = 0;
    for (const points of independent) {
      if ((points & vertices) === points) retained = Math.max(retained, size[points]);
    }
    const score = 16 * size[vertices] + retained;
    best[inside[vertices]] = Math.max(best[inside[vertices]], score);
  }
  for (let j = 0; j < edges.length; ++j) {
    const bit = 1 << j;
    for (let removed = 0; removed < edgeCount; ++removed) {
      if (removed & bit) best[removed] = Math.max(best[removed], best[removed ^ bit]);
    }
  }
  const exceptions = [];
  for (let removed = 0; removed < edgeCount; ++removed) {
    let minCover = 11;
    let minFull = 11;
    for (let vertices = 0; vertices < vertexCount; ++vertices) {
      if ((omitted[vertices] & ~removed) !== 0) continue;
      if (size[vertices] < minCover) {
        minCover = size[vertices];
        minFull = completion[vertices];
      } else if (size[vertices] === minCover) {
        minFull = Math.min(minFull, completion[vertices]);
      }
    }
    if (minCover !== 11 - (best[removed] >> 4) || minFull !== 11 - (best[removed] & 15))
      throw Error(`Mismatched cover minima at ${removed}`);
    if (minFull !== 7 && minFull !== 8) throw Error(`Unexpected full-cover size at ${removed}`);
    if (minFull === 8) exceptions.push([removed, minCover, minFull - minCover]);
  }
  if (exceptions.length !== 17) throw Error("Unexpected exception count");
  return {deletionSets: edgeCount, sevenVertexCompletions: edgeCount - exceptions.length, exceptions};
}

console.log(JSON.stringify(verifyNestedCovers(), null, 2));
