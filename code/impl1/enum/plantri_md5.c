/* plantri plugin: output only graphs with maximum degree <= 5.
   Build: see build_plantri.sh (cc -O3 -o plantri_md5 -DPLUGIN=plantri_md5.c plantri.c)
   The graphs of the class have degrees 3, 4, 5 (Theorem 4.1); degree >= 6 is impossible
   since 6 alpha(d) > 2 pi. The filter runs at output time, so counts (-u) are of the
   filtered class. */
#define FILTER md5_filter
static int md5_filter(int nbtot, int nbop, int doflip)
{
    int i;
    for (i = 0; i < nv; ++i)
        if (degree[i] > 5) return FALSE;
    return TRUE;
}
