/* plantri plugin for the rooted-map check: run as plantri_ms -p -G -u n [res/mod].
   For each output graph (3-connected, plane, one per isomorphism class with reflections) it counts
   the graphs per (F, nbtot), F = E - n + 2 the number of faces and nbtot = |Aut(G)| (the full group,
   exact with -G), and among them the class members: maximum degree <= 5 and every face of size <= 6.
   With -DMS_CHECK it also walks the faces of every graph and stops if their number is not F, or a
   vertex has degree < 3, or a face has size < 3. Build: build.sh. */
#define FILTER ms_filter
#define SUMMARY ms_summary
static unsigned long long ms_all[MAXF + 1][2 * MAXE + 1], ms_cls[MAXF + 1][2 * MAXE + 1];

/* Walks the faces; returns the largest face size, sets *nf to the number of faces and *minf to
   the smallest face size. A face is counted at its oriented edge of least address. */
static int ms_faces(int *nf, int *minf)
{
    int v, k, mx = 0, first;
    EDGE *e, *run;
    *nf = 0; *minf = MAXN;
    for (v = 0; v < nv; ++v)
    {
        e = firstedge[v];
        do
        {
            k = 0; first = 1; run = e;
            do { ++k; if (run < e) first = 0; run = run->invers->prev; } while (run != e);
            if (k > mx) mx = k;
            if (k < *minf) *minf = k;
            *nf += first;
            e = e->next;
        } while (e != firstedge[v]);
    }
    return mx;
}

static int ms_filter(int nbtot, int nbop, int doflip)
{
    int i, maxd = 0, mind = MAXN, F = ne / 2 - nv + 2, nf, minf, cls;
    for (i = 0; i < nv; ++i)
    {
        if (degree[i] > maxd) maxd = degree[i];
        if (degree[i] < mind) mind = degree[i];
    }
    if (nbtot < 1 || nbtot > 2 * ne || F < 1 || F > MAXF)
    {
        fprintf(stderr, "ms: out of range nbtot=%d F=%d\n", nbtot, F);
        exit(1);
    }
#ifdef MS_CHECK
    cls = (ms_faces(&nf, &minf) <= 6) && maxd <= 5;
    if (nf != F || mind < 3 || minf < 3)
    {
        fprintf(stderr, "ms: faces %d (Euler %d), min degree %d, min face %d\n", nf, F, mind, minf);
        exit(1);
    }
#else
    cls = maxd <= 5 && ms_faces(&nf, &minf) <= 6;
#endif
    ++ms_all[F][nbtot];
    if (cls) ++ms_cls[F][nbtot];
    return TRUE;
}

static void ms_summary(void)
{
    int F, a;
    unsigned long long g = 0, c = 0;
    for (F = 0; F <= MAXF; ++F)
        for (a = 0; a <= 2 * MAXE; ++a)
            if (ms_all[F][a])
            {
                fprintf(msgfile, "cell %d %d %d %llu %llu\n", nv, F, a, ms_all[F][a], ms_cls[F][a]);
                g += ms_all[F][a]; c += ms_cls[F][a];
            }
    fprintf(msgfile, "total %d %d %d %llu %llu\n", nv, res, mod, g, c);
}
