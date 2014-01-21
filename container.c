
/* ======================================================================
           KNAPSACK CONTAINER LOADING, David Pisinger 1998
   ====================================================================== */

/* This code solves the knapsack container loading problem, which
 * asks for an orthogonal packing of a given set of rectangular-shaped
 * boxes into a rectangular container such that the overall volume of
 * the packed boxes is maximized. Each box j=1,..,n is characterized by 
 * a width w_j, height h_j, and depth d_j, and the container has 
 * width W, height H and depth D. The boxes may be rotated in any
 * orthogonal direction, and no further restrictions are imposed.
 *
 * A description of this code is found in the following paper:
 *
 *   D.Pisinger (1999)
 *   "A tree search algorithm for the container loading problem"
 *   to appear in Ricerca Operativa.
 *
 * The present code is written in ANSI-C, and has been compiled with
 * the GNU-C compiler using option "-ansi -pedantic" as well as the
 * HP-UX C compiler using option "-Aa" (ansi standard).
 *
 * This file contains the callable routine binpack3d with prototype
 *   void contload(int n, int W, int H, int D,
 *             int *w, int *h, int *d, 
 *             int *x, int *y, int *z, int *k
 *             int *z);
 * the meaning of the parameters is the following:
 *   n         Size of problem, i.e. number of boxes to be packed.
 *   W,H,D     Width, height and depth of the container.
 *   w,h,d     Integer arrays of length n, where w[j], h[j], d[j]
 *             are the dimensions of box j for j=0,..,n-1. Since boxes
 *             may be rotated, these values may be permutated for each
 *             box upon return from the procedure.
 *   x,y,z     Integer arrays of length n where the solution found
 *             is returned. For each box j=0,..,n-1, the coordinates of 
 *             its lower-left-backward corner are given by x[j], y[j], z[j].
 *             are the coordinates of it lower-left-backward corner.
 *   k         Integer array of booleans, where k[j] indicates
 *             whether box j was packed into the container.
 *   vol       Volume of packed boxes (returned by the procedure)
 *
 * (c) Copyright, December 1998, 
 *   David Pisinger                     
 *   DIKU, University of Copenhagen      
 *   Universitetsparken 1              
 *   Copenhagen, Denmark               
 *
 * This code can be used free of charge for research and academic purposes
 * only.
 */              


/* ======================================================================
				   constants
   ====================================================================== */

#define MCUT2           8    /* level of search in 2d fill, normally 8 */
#define MCUT3           4    /* level of search in 3d fill, normally 4 */
#define MAXV           32    /* number of bits in a long integer       */
#define MAXSTATES   10000    /* max number of states in dynamic progr. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <stdarg.h>
#include <values.h>
#include <string.h>
#include <math.h>
#include <malloc.h>


/* ======================================================================
				   macros
   ====================================================================== */


#define VOL(i)           ((i)->dx * (long) (i)->dy * (i)->dz)
#define RECT(i)          ((i)->dx * (long) (i)->dy)
#define MIN(i,j)         ((i) < (j) ? (i) : (j))
#define MAX(i,j)         ((i) > (j) ? (i) : (j))
#define NO(a,p)          ((int) ((p) - (a)->fitem+1))
#define SIZE(a)          ((int) (((a)->lset+1)-(a)->fset))
#define SWAP(a, b)       { register item t; t = *(a); *(a) = *(b); *(b) = t; }
#define SWAPI(a, b)      { register itype t; t = (a); (a) = (b); (b) = t; }


/* ======================================================================
				 type declarations
   ====================================================================== */

typedef short         boolean; /* logical variable       */
typedef short         ntype;   /* number of states,bins  */
typedef short         itype;   /* can hold up to W,H,D   */
typedef long          stype;   /* can hold up to W*H*D   */
typedef double        ptype;   /* product type           */
typedef unsigned long btype;   /* binary solution vector */

typedef int (*funcptr) (const void *, const void *);

/* item record */
typedef struct ir {
  short    no;    /* item number */
  itype    dx;    /* box x-size */
  itype    dy;    /* box y-size */
  itype    dz;    /* box z-size */
  itype    x;     /* optimal x-position */
  itype    y;     /* optimal y-position */
  itype    z;     /* optimal z-position */
  struct ir *pair;/* pointer to paired item */
  itype    p;     /* knapsack profit */
  itype    w;     /* knapsack weight */
  boolean  k;     /* knapsack solution */
} item;

/* interval-stack for storing partially sorted intervals */
typedef struct { 
  item     *f;    /* pointer to first item in interval */
  item     *l;    /* pointer to last item in interval */
} interval;

/* state in KP dynamic programming */
typedef struct pv {
  stype    psum;  /* profit sum of state */
  stype    wsum;  /* weight sum of state */
  btype    vect;  /* partial solution vector */
} state;

/* set of states */
typedef struct pset {
  ntype    size;  /* set size */
  state    *fset; /* first element in set */
  state    *lset; /* last element in set */
  state    *set1; /* first element in array */
  state    *setm; /* last element in array */
} partset;

/* all problem information */
typedef struct {
  itype    mx;           /* x-size of container       */
  itype    my;           /* y-size of container       */
  itype    mz;           /* z-size of container       */
  stype    mcut;         /* area of slice of container */
  stype    lvol;         /* volume of current layer   */
  stype    mvol;         /* volume of container       */
  ntype    n;            /* number of items           */
  item     *fitem;       /* first item in problem     */
  item     *litem;       /* last item in problem      */
  item     *fsol;        /* first item in solution    */
  item     *lsol;        /* last item in solution     */
  itype    mindim;       /* currently smallest box length */
  itype    maxdim;       /* currently largest box length  */
  item     *g;           /* items before g are fixed   */
  item     *frect;       /* first item in rectangle solution */
  item     *lrect;       /* last item in rectangle solution */
  item     *rstart;      /* start of rectangle */
  stype    minloss;      /* the best filling found */
  stype    rectloss;     /* best loss in one layer (rectangle) */
  ntype    miss;         /* number of misses in best filling */
  int      lev;          /* number of layers in best filling */

  /* information corresponding to 0-1 Knapsack Problem */
  item     *h;           /* only consider items after h */
  item     *ftouch;
  item     *ltouch;
  item     *s;
  item     *t;
  item     *b;
  item     *fpart;
  item     *lpart;
  stype    wfpart;
  item     *fsort;
  item     *lsort;
  stype    wfsort;
  stype    c;
  stype    cstar;
  stype    wstar;        /* weight sum corresponding to zstar */
  stype    z;
  stype    lb;           /* lower bound on problem. vector y is not changed */
  stype    zstar;        /* optimal solution value */
  stype    zwsum;
  itype    ps, ws, pt, wt;

  btype    vno;          /* current vector number   */
  item *   vitem[MAXV];  /* current last MAXV items */
  item *   ovitem[MAXV]; /* optimal set of items    */
  btype    ovect;        /* optimal solution vector */

  stype    dantzig;
  stype    ub;
  stype    psumb;
  stype    wsumb;
  boolean  firsttime;
  boolean  welldef;
  partset  d;                 /* set of partial vectors */
  interval *intv1, *intv2;
  interval *intv1b, *intv2b;

  /* debug */
  long     iterates;          /* iterations in branch-and-bound */
  long     knapsacks;         /* number of knapsack problems solved */

} allinfo;


/* **********************************************************************
   **********************************************************************
                             Small procedures
   **********************************************************************
   ********************************************************************** */


/* =======================================================================
                                  error
   ======================================================================= */

void error(char *str, ...)
{
  va_list args;

  va_start(args, str);
  vprintf(str, args); printf("\n");
  va_end(args);
  printf("IRREGULAR PROGRAM TERMINATION\n");
  exit(-1);
}


/* ======================================================================
                                  palloc
   ====================================================================== */

/* Memory allocation and freeing, with implicit check */

void *palloc(long sz, long no)
{
  long size;
  void *p;

  size = sz * no;
  if (size == 0) size = 1;
  p = (void *) malloc(size);
  if (p == NULL) error("no memory size %ld", size);
  return p;
}

void pfree(void *p)
{
  if (p == NULL) error("freeing null");
  free(p);
}


/* ======================================================================
                                printitems
   ====================================================================== */

void printitems(allinfo *a)
{
  item *i;
  itype x1, y1, z1;
  FILE *trace;
  stype vol;
  char s[20];

  vol = 0;
  trace = fopen("trace.cont", "w");
  fprintf(trace,"printitems %d\n", (int) NO(a,a->litem));
  fprintf(trace," no [ dx, dy, dz] (    p,  w)   x   y   z pair kp active\n");
  for (i = a->fitem; i <= a->litem; i++) {
    x1 = i->dx; y1 = i->dy; z1 = i->dz;
    sprintf(s, "%3d  %1d  %c", (i->pair == NULL ? 0 : NO(a,i->pair)),
            i->k, ((i < a->g) ? '*' : ' '));
    fprintf(trace,"%3d [%3hd,%3hd,%3hd] (%5hd,%3hd) %3hd %3hd %3hd %s\n",
            NO(a,i), x1, y1, z1, i->p, i->w, i->x, i->y, i->z, s);
   if (i->k) vol += VOL(i);
  }
  fprintf(trace,"TOTAL VOLUME %ld OF %ld FILL %f\n",
          vol, a->mvol, vol/(double)(a->mvol));
  fclose(trace);
}


/* **********************************************************************
   **********************************************************************
                             0-1 Knapsack Problem
   **********************************************************************
   ********************************************************************** */

#define SYNC            5      /* when to switch to linear scan in bins */
#define SORTSTACK     200
#define MINMED        100      /* find exact median if larger size */

#define TRUE  1
#define FALSE 0

#define LEFT  1
#define RIGHT 2

#define PARTIATE 1
#define SORTALL  2

#define PMAX  1                /* profit of worlds most efficient item  */
#define WMAX  0                /* weight of worlds most efficient item  */
#define PMIN  0                /* profit of worlds least efficient item */
#define WMIN  1                /* weight of worlds least efficient item */

#define DET(a1, a2, b1, b2)    ((a1) * (ptype) (b2) - (a2) * (ptype) (b1))


/* ======================================================================
				  findvect
   ====================================================================== */

state *findvect(stype ws, state *f, state *l)
{
  /* find vector i, so that i->wsum <= ws < (i+1)->wsum */
  state *m;

  /* a set should always have at least one vector */
  if (f > l) error("findvect: empty set");
  if (f->wsum >  ws) return NULL;
  if (l->wsum <= ws) return l;

  while (l - f > SYNC) {
    m = f + (l - f) / 2;
    if (m->wsum > ws) l = m-1; else f = m;
  }
  while (l->wsum > ws) l--;
  return l;
}


/* ======================================================================
				push/pop
   ====================================================================== */

void push(allinfo *a, int side, item *f, item *l)
{
  interval *pos;
  if (l+1 == f) return;
  switch (side) {
    case LEFT : pos = a->intv1; (a->intv1)++; break;
    case RIGHT: pos = a->intv2; (a->intv2)--; break;
  }
  if (a->intv1 == a->intv2) error("interval stack full");
  pos->f = f; pos->l = l;
}

void pop(allinfo *a, int side, item **f, item **l)
{
  interval *pos;
  switch (side) {
    case LEFT : if (a->intv1 == a->intv1b) error("pop left");
		(a->intv1)--; pos = a->intv1; break;
    case RIGHT: if (a->intv2 == a->intv2b) error("pop right");
		(a->intv2)++; pos = a->intv2; break;
  }
  *f = pos->f; *l = pos->l;
}


/* ======================================================================
				improvesolution
   ====================================================================== */

void improvesolution(allinfo *a, state *v)
{
  if (v->wsum > a->c) error("wrong improvesoluton");
  if (v->psum < a->z) error("not improved solution");

  a->z      = v->psum;
  a->zwsum  = v->wsum;
  a->ovect  = v->vect;
  memcpy(a->ovitem, a->vitem, sizeof(item *) * MAXV);
}


/* ======================================================================
				definesolution
   ====================================================================== */

void definesolution(allinfo *a)
{
  register item *i, *m;
  item *f, *l;
  stype psum, wsum;
  btype j, k;

  if (a->firsttime) {
    if (a->z == a->lb) { a->welldef = TRUE; return; }
    a->zstar = a->z;
    a->wstar = a->zwsum;
    for (i = a->h+1, m = a->b; i != m; i++) i->k = 1;
    for (i = a->b, m = a->litem+1; i != m; i++) i->k = 0;
    a->firsttime = FALSE;
  }

  psum = a->z;
  wsum = a->zwsum;
  f    = a->fsort - 1;
  l    = a->lsort + 1;

  for (j = 0; j < MAXV; j++) {
    k = a->ovect & ((btype) 1 << j);
    i = a->ovitem[j]; if (i == NULL) continue;
    if (i->k == 1) {
      if (i > f) f = i;
      if (k) { psum += i->p; wsum += i->w; i->k = 0; }
    } else {
      if (i < l) l = i;
      if (k) { psum -= i->p; wsum -= i->w; i->k = 1; }
    }
  }

  a->welldef = (psum == a->psumb) && (wsum == a->wsumb);

  /* prepare for next round */
  if (!a->welldef) {
    a->fsort = f + 1;
    a->lsort = l - 1;
    a->intv1 = a->intv1b;
    a->intv2 = a->intv2b;

    a->c  = wsum;
    a->z  = psum - 1;
    a->ub = psum;

  }

}


/* ======================================================================
				partsort
   ====================================================================== */

void partsort(allinfo *a, item *f, item *l, stype ws, int what)
{
  register itype mp, mw;
  register item *i, *j, *m;
  register stype wi;
  int d;

  d = l - f + 1;
  if (d > 1) {
    m = f + d / 2;
    if (DET(f->p, f->w, m->p, m->w) < 0) SWAP(f, m);
    if (d > 2) {
      if (DET(m->p, m->w, l->p, l->w) < 0) {
        SWAP(m, l);
        if (DET(f->p, f->w, m->p, m->w) < 0) SWAP(f, m);
      }
    }
  }

  if (d > 3) {
    mp = m->p; mw = m->w; i = f; j = l; wi = ws;
    for (;;) {
      do { wi += i->w; i++; } while (DET(i->p, i->w, mp, mw) > 0);
      do {             j--; } while (DET(j->p, j->w, mp, mw) < 0);
      if (i > j) break;
      SWAP(i, j);
    }

    if (wi <= a->cstar) {
      if (what ==  SORTALL) partsort(a, f, i-1, ws, what);
      if (what == PARTIATE) push(a, LEFT, f, i-1);
      partsort(a, i, l, wi, what);
    } else {
      if (what ==  SORTALL) partsort(a, i, l, wi, what);
      if (what == PARTIATE) push(a, RIGHT, i,  l);
      partsort(a, f, i-1, ws, what);
    }
  }

  if ((d <= 3) || (what == SORTALL)) {
    a->fpart  = f;
    a->lpart  = l;
    a->wfpart = ws;
  }
}


/* ======================================================================
				  haschance
   ====================================================================== */

boolean haschance(allinfo *a, item *i, int side)
{
  register state *j, *m;
  register ptype p, w, r;
  register stype pp, ww;

  if (a->d.size == 0) return FALSE;

  if (side == RIGHT) {
    if (a->d.fset->wsum <= a->c - i->w) return TRUE;
    p = a->ps; w = a->ws; 
    pp = i->p - a->z - 1; ww = i->w - a->c;
    r = -DET(pp, ww, p, w);
    for (j = a->d.fset, m = a->d.lset + 1; j != m; j++) {
      if (DET(j->psum, j->wsum, p, w) >= r) return TRUE;
    }
  } else {
    if (a->d.lset->wsum > a->c + i->w) return TRUE;
    p = a->pt; w = a->wt; 
    pp = -i->p - a->z - 1; ww = -i->w - a->c;
    r = -DET(pp, ww, p, w);
    for (j = a->d.lset, m = a->d.fset - 1; j != m; j--) {
      if (DET(j->psum, j->wsum, p, w) >= r) return TRUE;
    }
  }
  return FALSE;
}


/* ======================================================================
				  multiply
   ====================================================================== */

void multiply(allinfo *a, item *h, int side)
{
  register state *i, *j, *k, *m;
  register itype p, w;
  register btype mask0, mask1;
  state *r1, *rm;

  if (a->d.size == 0) return;
  if (side == RIGHT) { p = h->p; w = h->w; } else { p = -h->p; w = -h->w; }
  if (2*a->d.size + 2 > MAXSTATES) error("no space in multiply");

  /* keep track on solution vector */
  a->vno++;
  if (a->vno == MAXV) a->vno = 0;
  mask1 = ((btype) 1 << a->vno);
  mask0 = ~mask1;
  a->vitem[a->vno] = h;

  /* initialize limits */
  r1 = a->d.fset; rm = a->d.lset; k = a->d.set1; m = rm + 1;
  k->psum = -1;
  k->wsum = r1->wsum + abs(p) + 1;
  m->wsum = rm->wsum + abs(w) + 1;

  for (i = r1, j = r1; (i != m) || (j != m); ) {
    if (i->wsum <= j->wsum + w) {
      if (i->psum > k->psum) {
        if (i->wsum > k->wsum) k++;
        k->psum = i->psum; k->wsum = i->wsum;
        k->vect = i->vect & mask0;
      }
      i++;
    } else {
      if (j->psum + p > k->psum) {
        if (j->wsum + w > k->wsum) k++;
        k->psum = j->psum + p; k->wsum = j->wsum + w;
        k->vect = j->vect | mask1;
      }
      j++;
    }
  }

  a->d.fset = a->d.set1;
  a->d.lset = k;
  a->d.size  = a->d.lset - a->d.fset + 1;
}


/* =========================================================================
				   simpreduce
   ========================================================================= */

void simpreduce(int side, item **f, item **l, allinfo *a)
{
  register item *i, *j, *k;
  register ptype pb, wb;
  register ptype q, r;
  register int redu;

  if (a->d.size == 0) { *f = *l+1; return; }
  if (*l < *f) return;

  pb = a->b->p; wb = a->b->w;
  q = DET(a->z+1-a->psumb, a->c-a->wsumb, pb, wb);
  r = -DET(a->z+1-a->psumb, a->c-a->wsumb, pb, wb);
  i = *f; j = *l;
  redu = 0;
  if (side == LEFT) {
    k = a->fsort - 1;
    while (i <= j) {
      if (DET(j->p, j->w, pb, wb) > r) {
        SWAP(i, j); i++; redu++;       /* not feasible */
      } else {
        SWAP(j, k); j--; k--;  /* feasible */
      }
    }
    *l = a->fsort - 1; *f = k + 1;
  } else {
    k = a->lsort + 1;
    while (i <= j) {
      if (DET(i->p, i->w, pb, wb) < q) {
        SWAP(i, j); j--; redu++;      /* not feasible */
      } else {
        SWAP(i, k); i++; k++;  /* feasible */
      }
    }
    *f = a->lsort + 1; *l = k - 1;
  }
}


/* ======================================================================
				  reduceset
   ====================================================================== */

void reduceset(allinfo *a)
{
  register state *i, *m, *k;
  register ptype ps, ws, pt, wt, r;
  stype z, c;
  state *r1, *rm, *v;
  item *f, *l;

  if (a->d.size == 0) return;

  /* initialize limits */
  r1 = a->d.fset; rm = a->d.lset;
  v  = findvect(a->c, r1, rm);
  if (v == NULL) v = r1 - 1; /* all states infeasible */
  else { if (v->psum > a->z) improvesolution(a, v); }

  c = a->c; z = a->z + 1; k = a->d.setm;

  /* expand core, and choose ps, ws */
  if (a->s < a->fsort) {
    if (a->intv1 == a->intv1b) {
      ps = PMAX; ws = WMAX;
    } else {
      pop(a, LEFT, &f, &l);
      if (f < a->ftouch) a->ftouch = f;
      ps = f->p; ws = f->w; /* default: pick first item */
      simpreduce(LEFT, &f, &l, a);
      if (f <= l) {
        partsort(a, f, l, 0, SORTALL); a->fsort = f;
        ps = a->s->p; ws = a->s->w;
      }
    }
  } else {
    ps = a->s->p; ws = a->s->w;
  }

  /* expand core, and choose pt, wt */
  if (a->t > a->lsort) {
    if (a->intv2 == a->intv2b) {
      pt = PMIN; wt = WMIN;
    } else {
      pop(a, RIGHT, &f, &l);
      if (l > a->ltouch) a->ltouch = l;
      pt = l->p; wt = l->w; /* default: pick first item */
      simpreduce(RIGHT, &f, &l, a);
      if (f <= l) {
        partsort(a, f, l, 0, SORTALL); a->lsort = l;
        pt = a->t->p; wt = a->t->w;
      }
    }
  } else {
    pt = a->t->p; wt = a->t->w;
  }

  /* now do the reduction */
  r = DET(z, c, ps, ws);
  for (i = rm, m = v; i != m; i--) {
    if (DET(i->psum, i->wsum, ps, ws) >= r) {
      k--; *k = *i;
    }
  }

  r = DET(z, c, pt, wt);
  for (i = v, m = r1 - 1; i != m; i--) {
    if (DET(i->psum, i->wsum, pt, wt) >= r) {
      k--; *k = *i;
    }
  }

  a->ps = ps; a->ws = ws;
  a->pt = pt; a->wt = wt;
  a->d.fset = k;
  a->d.lset = a->d.setm - 1; /* reserve one record for multiplication */
  a->d.size = a->d.lset - a->d.fset + 1;
}


/* ======================================================================
				  initfirst
   ====================================================================== */

void initfirst(allinfo *a, stype ps, stype ws)
{
  state *k;

  a->d.size  = 1;
  a->d.set1  = palloc(MAXSTATES, sizeof(state));
  a->d.setm  = a->d.set1 + MAXSTATES - 1;
  a->d.fset  = a->d.set1;
  a->d.lset  = a->d.set1;

  k = a->d.fset;
  k->psum   = ps;
  k->wsum   = ws;
  k->vect   = 0;
}


/* ======================================================================
				  initvect
   ====================================================================== */

void initvect(allinfo *a)
{
  register btype i;

  for (i = 0; i < MAXV; i++) a->vitem[i] = NULL;
  a->vno = MAXV-1;
}


/* ======================================================================
				findbreak
   ====================================================================== */

void findbreak(allinfo *a)
{
  register item *i, *m;
  register stype psum, wsum, c;

  psum = 0; wsum = 0; c = a->cstar;
  for (i = a->h+1, m = a->litem+1; ; i++) {
    if (i == m) break;
    if (wsum + i->w > c) break;
    psum += i->p; wsum += i->w;
  }

  a->fsort   = a->fpart;
  a->lsort   = a->lpart;
  a->ftouch  = a->fpart;
  a->ltouch  = a->lpart;
  a->b       = i;
  a->psumb   = psum;
  a->wsumb   = wsum;
  a->zwsum   = 0;
  a->dantzig = (i == m ? psum : psum + ((c - wsum) * (stype) i->p) / i->w);

  /* find greedy solution */
  for (i = a->b, m = a->litem+1; i != m; i++) {
    if (wsum + i->w <= c) { psum += i->p; wsum += i->w; }
  }

  if (psum > a->lb) {
    for (i = a->h+1, m = a->b; i != m; i++) i->k = 1;
    for (i = a->b, m = a->litem+1, wsum = a->wsumb; i != m; i++) {
      i->k = 0; if (wsum + i->w <= c) { wsum += i->w; i->k = 1; }
    }
    a->lb    = psum;
    a->z     = psum;
    a->zstar = psum;
    a->wstar = wsum;
  } else {
    a->z     = a->lb;
    a->zstar = a->lb;
    a->wstar = a->cstar;
  }
  a->c = a->cstar;
}


/* ======================================================================
				minknap
   ====================================================================== */

void minknap(allinfo *a, item *fitem, stype c)
{
  interval *inttab;

  a->h = fitem-1;

  a->cstar = c;
  a->lb    = 0;
  inttab   = palloc(sizeof(interval), SORTSTACK);
  a->intv1 = a->intv1b = &inttab[0];
  a->intv2 = a->intv2b = &inttab[SORTSTACK - 1];
  a->fsort = a->litem; a->lsort = a->h+1;
  partsort(a, a->h+1, a->litem, 0, PARTIATE);
  findbreak(a);

  a->ub = a->dantzig;
  a->firsttime = TRUE;

  for (;;) {
    a->s = a->b-1;
    a->t = a->b;
    initfirst(a, a->psumb, a->wsumb);
    initvect(a);
    reduceset(a);

    while ((a->d.size > 0) && (a->z != a->ub)) {
      if (a->t <= a->lsort) {
	if (haschance(a, a->t, RIGHT)) multiply(a, a->t, RIGHT);
	(a->t)++;
      }
      reduceset(a);

      if (a->s >= a->fsort) {
	if (haschance(a, a->s, LEFT)) multiply(a, a->s, LEFT);
	(a->s)--;
      }
      reduceset(a);
    }
    pfree(a->d.set1);

    definesolution(a);
    if (a->welldef) break;
  }

  pfree(inttab);
}



/* **********************************************************************
   **********************************************************************
                             container loading
   **********************************************************************
   ********************************************************************** */


/* ======================================================================
                              finddimensions
   ====================================================================== */

void finddimensions(allinfo *a)
{
  register item *i, *m;
  register itype mindim, maxdim;

  /* find smallest/largest dimension globally, and order items */
  mindim = a->mx + a->my + a->mz; maxdim = 0; 
  for (i = a->g, m = a->litem+1; i != m; i++) {
    if (i->dx < mindim) mindim = i->dx;
    if (i->dy < mindim) mindim = i->dy;
    if (i->dz < mindim) mindim = i->dz;
    if (i->dx > maxdim) maxdim = i->dx;
    if (i->dy > maxdim) maxdim = i->dy;
    if (i->dz > maxdim) maxdim = i->dz;
  }
  a->mindim = mindim;
  a->maxdim = maxdim;
}


/* ======================================================================
                              findminmax
   ====================================================================== */

void findminmax(allinfo *a)
{
  register item *i, *m;
  register itype mindim, maxdim;

  /* find smallest/largest dimension in rectangle */
  mindim = maxdim = a->g->dx;
  for (i = a->g, m = a->litem+1; i != m; i++) {
    if (i->dx < mindim) mindim = i->dx;
    if (i->dy < mindim) mindim = i->dy;
    if (i->dx > maxdim) maxdim = i->dx;
    if (i->dy > maxdim) maxdim = i->dy;
  }
  a->mindim = mindim;
  a->maxdim = maxdim;
}


/* ======================================================================
                                findfits
   ====================================================================== */

stype findfits(allinfo *a, itype dz)
{
  register item *i, *m;
  register stype vol;

  /* find lost space if all items fit at layer */
  vol = a->mcut * dz;
  for (i = a->g, m = a->litem+1; i != m; i++) {
    if ((i->dx <= dz) || (i->dy <= dz) || (i->dz <= dz)) vol -= VOL(i);
  }
  return MAX(0, vol);
}



/* ======================================================================
                                 givedim
   ====================================================================== */

void givedim(item *i, int h, itype *x, itype *y, itype *z)
{
  switch (h) {
    case 0: *x = i->dy; *y = i->dz; *z = i->dx; break;
    case 1: *x = i->dx; *y = i->dz; *z = i->dy; break;
    case 2: *x = i->dx; *y = i->dy; *z = i->dz; break;
  }
}


/* ======================================================================
                                 bestmatch
   ====================================================================== */

#define epsilon  0.000001

void bestmatch(item *s, item *i, itype z, itype mindim,
               item **pair, int *h1, int *k1, double *mfill)
{
  register item *j;
  itype ix, iy, iz, jx, jy, jz, sx, sy, sz;
  double fill, jfill;
  int h, k, a[3], b[3];

  *pair = NULL; *h1 = *k1 = 0;
  if (i->dx + mindim > z) return;
  *mfill = VOL(i)/(double)(i->w*(long)z);
  a[0] = i->dx; a[1] = i->dy; a[2] = i->dz;
  for (j = s; j != i; j++) {
    if (i->dx + j->dx > z) continue; /* smallest sides do not fit in z */
    jfill = VOL(j)/(double)(j->w*(long)z);
    b[0] = j->dx; b[1] = j->dy; b[2] = j->dz;
    for (h = 0, k = 2; h != 3; h++) {
      while (a[h] + b[k] > z) { k--; if (k < 0) break; }
      if (k < 0) break;
      iz = a[h]; jz = b[k]; sz = iz + jz;  if (sz > z) error("bad match");
      switch (h) {
        case 0: ix = a[1]; iy = a[2]; break;
        case 1: ix = a[0]; iy = a[2]; break;
        case 2: ix = a[0]; iy = a[1]; break;
      }
      switch (k) {
        case 0: jx = b[1]; jy = b[2]; break;
        case 1: jx = b[0]; jy = b[2]; break;
        case 2: jx = b[0]; jy = b[1]; break;
      }
      sx = MAX(ix, jx); sy = MAX(iy, jy);
      fill = (VOL(i)+VOL(j))/(double)(sx*(long)sy*z);
      if ((fill > *mfill + epsilon) && (fill > jfill + epsilon)) {
        *h1 = h; *k1 = k; *mfill = fill; *pair = j;
      }
    }
  }
}


/* ======================================================================
                                turnboxes
   ====================================================================== */

item *turnboxes(allinfo *a, itype z)
{
  register item *i, *m, *s;
  itype ix, iy, iz, jx, jy, jz, sx, sy, sz;
  double mfill;
  int h1, k1;
  item *j;

  /* this routine prepares a z-layer */
  ix = iy = iz = jx = jy = jz = 0; 
  for (i = s = a->g, m = a->litem+1; i != m; i++) {
    /* items are turned such that dx <= dy <= dz */
    if (i->dx > i->dy) SWAPI(i->dx, i->dy); 
    if (i->dy > i->dz) SWAPI(i->dy, i->dz);
    if (i->dx > i->dy) SWAPI(i->dx, i->dy);
    if (i->dx > i->dy || i->dy > i->dz) error("bad ordering\n");
    i->x = i->y = i->z = i->p = 0; i->k = FALSE; i->pair = NULL; 
    if (i->dx > z) { SWAP(s,i); s++; continue; } /* not feasible */
    if (i->dz <= z) { i->w = i->dx * i->dy; continue; }
    if (i->dy <= z) { i->w = i->dx * i->dz; continue; }
    if (i->dx <= z) { i->w = i->dy * i->dz; continue; }
    error("do not fit"); 
  }
  if (s > a->litem) { printitems(a); error("no feasible boxes dz=%d", z); }

  /* try to pair two boxes */
  for (i = a->litem; i != s-1; i--) {
    bestmatch(s, i, z, a->mindim, &j, &h1, &k1, &mfill);

    if (j != NULL) {
      /* always place biggest in front */
      givedim(i, h1, &ix, &iy, &iz); givedim(j, k1, &jx, &jy, &jz);
      if (ix * (long) iy < jx * (long) jy) { SWAP(i,j); SWAPI(h1,k1); }

      /* now do the pairing */
      j->p = 0; i->p = (VOL(i)+VOL(j))/100;   
      givedim(i, h1, &ix, &iy, &iz); givedim(j, k1, &jx, &jy, &jz);
      sx = MAX(ix, jx); sy = MAX(iy, jy); 
      sz = iz + jz; if (sz > z) error("bad pair"); 
      j->dx = jx; j->dy = jy; j->dz = jz;
      j->x  = ix; j->y  = iy; j->z  = iz;
      i->dx = sx; i->dy = sy; i->dz = sz;
      i->pair = s; SWAP(s,j); s++;
    } else {
      /* single item: turn such that fits in z-layer */
      i->p = VOL(i)/100; /* profit is original volume */
      if (i->dz <= z) continue; 
      if (i->dy <= z) { SWAPI(i->dy, i->dz); continue; } 
      if (i->dx <= z) { SWAPI(i->dx, i->dz); SWAPI(i->dx, i->dy); }
    }
  }
  return s;
}


/* ======================================================================
                               restorelayer
   ====================================================================== */

item *restorelayer(allinfo *a, item *fitem, itype dz)
{
  register item *i, *j, *m, *s;
  stype vol;
  itype sx;

  /* update solution variables in pairs */
  for (i = fitem, m = a->litem+1; i != m; i++) {
    i->p = 0; /* item in front */
    if ((i->k) && (i->pair)) { i->pair->w = i->w; i->pair->p = i->pair->k = 1; }
  }

  /* split pairs */
  for (i = fitem, m = a->litem+1; i != m; i++) {
    if (i->pair != NULL) {
      j = i->pair; sx = MAX(j->x, j->dx); /* check if box was turned */
      if (sx != i->dx) { SWAPI(j->x, j->y); SWAPI(j->dx, j->dy); }
      /* split combined box i, into original boxes */
      i->dx = j->x; i->dy = j->y; i->dz = j->z;
      j->x  = i->x; j->y  = i->y; j->z  = i->z+i->dz;
      if (i->dx*(long)i->dy < j->dx*(long)j->dy) error("bad front/back pair");
      i->pair = NULL;
    }
  }

  /* swap chosen items to beginning of table */
  s = fitem; vol = a->lvol;
  for (i = fitem, m = a->litem+1; i != m; i++) {
    if (i->k) { vol -= VOL(i); i->k = dz; SWAP(s,i); s++; } else { i->w = 0; }
  }
  if (vol > a->rectloss) error("increased loss %ld %ld\n", vol, a->rectloss);
  if (vol < 0) { printitems(a); error("neg loss %ld %ld\n", vol, a->rectloss); }
  a->rectloss = vol;
  return s;
}


/* ======================================================================
                                findlargest
   ====================================================================== */

void findlargest(allinfo *a, itype *t, itype maxd, int no)
{
  /* return a table "t" of "no" largest box lengths <= "maxd"  */
  register item *i, *m;
  int *occ, j, k, lj, mx;
  itype *h;

  /* alloc space */
  occ = palloc(sizeof(int), a->maxdim+1);

  /* find occurences of each weight */
  for (j = a->maxdim, lj = a->mindim-1; j != lj; j--) occ[j] = 0;
  for (i = a->g, m = a->litem+1; i != m; i++) {
    occ[i->dx]++; occ[i->dy]++; occ[i->dz]++;
  }

  /* find the "no" largest occurences, such that */
  /* the number of occurences must be increasing */
  j = MIN(maxd, a->maxdim);
  for (h = t, k = 0, lj = a->mindim-1, mx = 0; j != lj; j--) {
    if (occ[j] > k) { *h = j; h++; k++; mx = occ[j]; if (k == no) break; }
  }
  if (k < no) *h = 0; /* place 0 when number of boxes < "no" */
  pfree(occ);
}


/* ======================================================================
                                findcommon
   ====================================================================== */

void findcommon(allinfo *a, itype *t, itype maxd, int no)
{
  /* return a table of "no" most common box lengths */
  register item *i, *m;
  int *occ, j, k, lj, mx;
  itype *h;

  /* alloc space */
  occ = palloc(sizeof(int), a->maxdim+1);

  /* find occurences of each weight */
  for (j = a->maxdim, lj = a->mindim-1; j != lj; j--) occ[j] = 0;
  for (i = a->g, m = a->litem+1; i != m; i++) {
    occ[i->dx]++; occ[i->dy]++;
  }

  /* new version, which chooses biggest, increasing frequency */
  j = MIN(maxd, a->maxdim);
  for (h = t, k = 0, lj = a->mindim-1, mx = 1; j != lj; j--) {
    if (occ[j] > k/2) { *h = j; h++; k++; mx = occ[j]; if (k == no) break; }
  }
  if (k < no) *h = 0; /* place 0 when number of boxes < "no" */
  pfree(occ);
}


/* ======================================================================
                                 prepare
   ====================================================================== */

item *prepare(allinfo *a, item *fitem, itype dx)
{
  register item *i, *m, *s;
  itype no;

  /* prepare for knapsack solution: turn items such that they fit */
  for (i = s = fitem, m = a->litem+1, no = 0; i != m; i++) {
    i->k = FALSE;
    if (i->dy < i->dx) SWAPI(i->dx, i->dy); /* ensure x < y */
    if (i->dy <= dx) SWAPI(i->dx, i->dy); /* y dimension fits, rotate */
    if (i->dx > dx) { SWAP(s,i); s++; continue; } /* not feasible */
    i->w = i->dy; /* profit initialized when layer prepared */
    no++;
  }
  return s;
}


/* ======================================================================
                                 givex
   ====================================================================== */

stype givex(allinfo *a, item *fitem, itype x, itype y, itype z,
            itype *dx, boolean xdir)
{
  register item *i, *m, *s;
  stype vsum;
  itype d;

  s = a->g; vsum = 0; d = 0;
  for (i = fitem, m = a->litem+1; i != m; i++) {
    if (i->k) {
      i->x = x; i->y = y; i->z = z; i->w = z; 
      if (i->dx > d) d = i->dx;
      if (xdir) SWAPI(i->dx, i->dy);
      if (xdir) x += i->dx; else y += i->dy;
      vsum += i->p * (long) 100;
      SWAP(s,i); s++;
    }
  }
  if (d < *dx) { *dx = d; }
  a->g = s;
  return vsum;
}


/* ======================================================================
                                 onestrip
   ====================================================================== */

stype onestrip(allinfo *a, itype x, itype y, itype z,
               itype *dx, itype dy, boolean xdim)
{
  item *fitem;

  fitem = prepare(a, a->g, *dx);
  if (fitem > a->litem) return 0; /* no items fit, return fill=0, same dx */
  a->knapsacks++;
  minknap(a, fitem, dy);
  return givex(a, fitem, x, y, z, dx, xdim);
}


/* ======================================================================
                                  savesol
   ====================================================================== */

void savesol(allinfo *a, stype loss)
{
  item *i, *m;
  stype vol;

  /* set i->k = 0 in not chosen items */
  for (i = a->g, m = a->litem+1; i != m; i++) { i->x = i->y = i->z = i->k = 0; }

  /* check loss */
  vol = a->lvol; m = a->litem+1;
  for (i = a->rstart; i != m; i++) if (i->k) vol -= i->p * (long)100;
  if (vol != loss) { printitems(a); error("bad impr %ld %ld\n", vol, loss); }
  if (vol < 0) { printitems(a); error("neg impr %ld %ld\n", vol, loss); }

  /* save solution in extra array */
  memcpy(a->frect, a->fitem, a->n * sizeof(item));
  a->rectloss = loss;
}


/* ======================================================================
                                striprecurs
   ====================================================================== */

void striprecurs(allinfo *a, stype oldloss, boolean xdir,
                 itype x, itype y, itype z, itype dz)
{
  item *saveg, *gafter;
  itype c, b, mx, my, md, dx, h, x1, y1, d[MCUT2];
  stype loss, vol;

  /* fill a strip, such that the knapsack runs in xdir direction */
  /* first, find dimensions and remove items which do not fit */
  mx = a->mx - x;
  my = a->my - y;
  md = MIN(mx, my);
  saveg = prepare(a, a->g, md); /* remove items which do not fit */
  c = (xdir ? mx : my); /* length of rectangle */
  b = (xdir ? my : mx); /* width of rectangle */

  if (saveg > a->litem) {
    /* if no more items fit, update and return */
    loss = oldloss + mx * (long)my * dz;
    if (loss < a->rectloss) savesol(a, loss);
  } else {
    /* choose largest sizes, and pack  */
    findcommon(a, d, b, MCUT2);
    for (h = 0, dx = d[0]+1; h != MCUT2; h++) {
      if (d[h] == 0) break;     /* d[.] is terminated with null */
      if (d[h] >= dx) continue; /* since decresing dx, has been considered */
      dx = d[h]; a->g = saveg; 
      vol = onestrip(a, x, y, z, &dx, c, xdir); /* dx may squeeze */
      loss = oldloss + dx * (long)c * dz - vol; 
      if (loss >= a->rectloss) continue;
      if (loss < 0) { printitems(a); error("neg strip"); }
      if (dx == 0) a->g = a->litem+1;   /* no fits, but perhaps improved */
      x1 = (xdir ? x : x+dx); y1 = (xdir ? y+dx : y); gafter = a->g;
      striprecurs(a, loss, (md < 3*a->maxdim/2 ? xdir : !xdir), x1, y1, z, dz);
      if (md < 3*a->maxdim/2) continue; /* if only two strips fit, same dir */
      a->g = gafter; striprecurs(a, loss, xdir, x1, y1, z, dz);
    }
  }
}


/* ======================================================================
                                rectangle
   ====================================================================== */

stype rectangle(allinfo *a, itype z, itype dz)
{
  /* prepare layer */
  a->rstart   = a->g;
  a->g        = turnboxes(a, dz); /* turn boxes to fit layer */
  a->lvol     = a->mx * (long) a->my * dz; /* volume of current layer */
  a->rectloss = a->lvol;
  findminmax(a); savesol(a, a->lvol); /* save empty solution */

  /* call recursive part */
  striprecurs(a, 0, TRUE, 0, 0, z, dz);

  /* choose best solution */
  memcpy(a->fitem, a->frect, a->n * sizeof(item));

  /* split pairs */
  a->g = restorelayer(a, a->rstart, dz); /* split pairs */
  return a->rectloss; /* return loss at this layer */
}


/* ======================================================================
                                branch
   ====================================================================== */

boolean branch(allinfo *a, item *f, itype z, stype oldloss, int levels)
{
  itype d[MCUT3], dz;
  stype loss;
  double fill;
  boolean ok;
  int j;

  a->iterates++; a->g = f;
  finddimensions(a);

  /* check if only space for one layer */
  if ((a->mz - z < a->maxdim) || (a->g > a->litem)) {
    dz = a->mz - z; 
    if ((dz < a->mindim) || (a->g > a->litem)) loss = oldloss + a->mcut * dz;
    else {
      loss = oldloss + findfits(a, dz);
      if (loss < a->minloss) loss = oldloss + rectangle(a, z, dz);
    }
    if (loss < a->minloss) {
      a->minloss = loss; a->miss = a->litem - a->g + 1; a->lev = levels;
      fill = (a->mvol - loss) / (double) a->mvol;
      memcpy(a->fsol, a->fitem, a->n * sizeof(item));
      printf("IMPROVE %f, MISS %d\n", fill, a->miss);
    }
    return (a->miss == 0);
  }

  /* more layers, thus branch */
  ok = FALSE;
  findlargest(a, d, a->mz - z, MCUT3);
  for (j = 0; j != MCUT3; j++) {
    a->g = f; dz = d[j]; if (dz <= a->maxdim/2) continue; 
    loss = oldloss + rectangle(a, z, dz);
    if (loss < a->minloss) ok = branch(a, a->g, z+dz, loss, levels+1);
    if (ok) break;
  }
  return ok;
}


/* ======================================================================
                                inititems
   ====================================================================== */

void inititems(allinfo *a, int *w, int *h, int *d)
{
  item *i, *m;
  int j;

  for (i = a->fitem, m = a->litem+1, j = 0; i != m; i++, j++) {
    i->no = j+1; i->dx = w[j]; i->dy = h[j]; i->dz = d[j];
  }

  for (i = a->fitem, m = a->litem+1; i != m; i++) {
    i->x = i->y = i->z = i->p = i->w = i->k = 0; i->pair = NULL; 
  }
}


/* ======================================================================
                                returnitems
   ====================================================================== */

void returnitems(allinfo *a, int *w, int *h, int *d, 
                 int *x, int *y, int *z, int *k, int *vol)
{
  stype svol;
  item *i, *m;
  int j;

  for (i = a->fsol, m = a->lsol+1, svol = 0; i != m; i++) {
    if (i->k) svol += VOL(i);
    j = i->no-1; w[j] = i->dx; h[j] = i->dy; d[j] = i->dz; 
    x[j] = i->x; y[j] = i->y; z[j] = i->z; k[j] = i->k;
  }
  *vol = svol;
}



/* ======================================================================
                                contload
   ====================================================================== */

void contload(int n, int W, int H, int D, 
              int *w, int *h, int *d,
              int *x, int *y, int *z, int *k,
              int *vol)
{
  allinfo a;
  item *t;

  /* allocate space for test example */
  t           = palloc(n, sizeof(item));
  a.n         = n; 
  a.fitem     = t; 
  a.litem     = t + n - 1; 
  a.mx        = W; 
  a.my        = H;
  a.mz        = D;
  a.fsol      = palloc(n, sizeof(item));
  a.lsol      = a.fsol + n - 1;
  a.frect     = palloc(n, sizeof(item));
  a.mcut      = W * (long) H;   
  a.mvol      = a.mcut * D;
  a.minloss   = a.mvol;
  a.iterates  = 0;
  a.knapsacks = 0;

  /* copy items to internal structure */
  inititems(&a, w, h, d);

  /* now the iterative heuristic */
  a.g = a.fitem; /* consider items from a.g */
  branch(&a, a.fitem, 0, 0, 1);

  /*  copy items back to solution vector */
  returnitems(&a, w, h, d, x, y, z, k, vol);
   
  /* clean up */
  pfree(t);
  pfree(a.fsol);
  pfree(a.frect);
}


