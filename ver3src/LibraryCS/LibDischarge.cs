using System;
using System.Diagnostics;


namespace LibraryCS2 {
  public static class LibDischargeReduce {
    public const int CARTVERT    = 5 * 12 + 2;     // domain of l_A, u_A, where A is an axle
    public const int MAXELIST    = 134;            // length of edgelist[a][b]
    public const int MAXASTACK   = 5;              // max height of Astack (see "Reduce")
    public const int VERTS       = 27;	/* max number of vertices in a free completion + 1 */
    public const int DEG         = 13;	/* max degree of a vertex in a free completion + 1, must be at least 13 because of row 0 */

    public record TpAxle(int[][] low, int[][] upp, int lev);
    public record TpAdjmat(int[][] adj);
    public record TpEdgelist(int[][][] edg);
    public record TpQuestion(int[] qa, int[] qb, int[] qc, int[] qd);
    public record TpVertices(int[] ver);
    public record TpReduceRet(bool retB, TpAxle axle, bool[] used, TpVertices image);
    public record TpReducePack1(TpAxle axle, int[] bLow, int[] bUpp, TpAdjmat adjmat);
    public record TpReducePack2(TpEdgelist edgelist, bool[] used, TpVertices image);
    // typedef long tp_confmat[VERTS][DEG];

    public static TpReducePack1 rp1;
    public static TpReducePack2 rp2;
    public static TpQuestion[] redquestions = new TpQuestion[633];

    /*********************************************************************
      Getadjmat
    Computes adjmat defined as follows. Let G=G(L), where L is the
    skeleton of A. Notice that G only depends on u_B(i) for i=0,1,..,deg.
    Then adjmat[u][v]=w if u,v,w form a clockwise triangle in G, and
    adjmat[u][v]=-1 if w does not exist.
    *********************************************************************/
    public static void Getadjmat(int naxles, TpAxle aa, TpAdjmat adjmat)
    {
      int deg, a, b, h, i;

      deg = aa.low[naxles][0];
      for (a = 0; a < CARTVERT; a++)
        for (b = 0; b < CARTVERT; b++)
          adjmat.adj[a][b] = -1;
      for (i = 1; i <= deg; i++) {
        h = (i == 1) ? deg : i - 1;
        adjmat.adj[0][h] = i;
        adjmat.adj[i][0] = h;
        adjmat.adj[h][i] = 0;
        a = deg + h;
        adjmat.adj[i][h] = a;
        adjmat.adj[a][i] = h;
        adjmat.adj[h][a] = i;
        if (aa.upp[naxles][i] < 9)
          DoFan(deg, i, aa.upp[naxles][i], adjmat);
      }
    }/* Getadjmat */

    /*********************************************************************
      DoFan
    Does one fan of adjmat
    *********************************************************************/
    public static void DoFan(int deg, int i, int k, TpAdjmat adjmat)
    {
      int a, b, c, d, e;

      a = i == 1 ? 2 * deg : deg + i - 1;
      b = deg + i;
      if (k == 5) {
        adjmat.adj[i][a] = b;
        adjmat.adj[a][b] = i;
        adjmat.adj[b][i] = a;
        return;
      }
      c = 2 * deg + i;
      adjmat.adj[i][a] = c;
      adjmat.adj[a][c] = i;
      adjmat.adj[c][i] = a;
      if (k == 6) {
        adjmat.adj[i][c] = b;
        adjmat.adj[c][b] = i;
        adjmat.adj[b][i] = c;
        return;
      }
      d = 3 * deg + i;
      adjmat.adj[i][c] = d;
      adjmat.adj[c][d] = i;
      adjmat.adj[d][i] = c;
      if (k == 7) {
        adjmat.adj[i][d] = b;
        adjmat.adj[d][b] = i;
        adjmat.adj[b][i] = d;
        return;
      }
      e = 4 * deg + i;
      adjmat.adj[i][d] = e;
      adjmat.adj[d][e] = i;
      adjmat.adj[e][i] = d;
      adjmat.adj[i][e] = b;
      adjmat.adj[e][b] = i;
      adjmat.adj[b][i] = e;
    }/* DoFan */

    /**********************************************************************
      GetEdgeList
    For (a,b) such that a >= b, b <= 8 and a <= 11 computes X=edgelist[a][b]
    defined as follows: X[2*i+1],X[2*i+2] (i=0,1,...,X[0]-1) are all pairs of
    adjacent vertices u,v of the skeleton of A with degrees a,b, respectively
    such that either a<=8 or u=0.
    ***********************************************************************/
    public static void GetEdgelist(
      int naxles, TpAxle aa, TpEdgelist edgelist)
    {
      int a, b, c, d, e, h, i, deg;

      deg = aa.low[naxles][0];
      for (a = 5; a <= 11; a++)
          for (b = 5; b <= 8 && b <= a; b++)
      edgelist.edg[a][b][0] = 0;
      for (i = 1; i <= deg; i++) {
        AddToList(edgelist, 0, i, aa.upp[naxles]);
        h = (i == 1) ? deg : i - 1;
        AddToList(edgelist, i, h, aa.upp[naxles]);
        a = deg + h;
        b = deg + i;
        AddToList(edgelist, i, a, aa.upp[naxles]);
        AddToList(edgelist, i, b, aa.upp[naxles]);
        if (aa.low[naxles][i] != aa.upp[naxles][i])
          continue;
        /* in this case we are not interested in the fan edges */
        if (aa.upp[naxles][i] == 5) {
          AddToList(edgelist, a, b, aa.upp[naxles]);
          continue;
        }
        c = 2 * deg + i;
        AddToList(edgelist, a, c, aa.upp[naxles]);
        AddToList(edgelist, i, c, aa.upp[naxles]);
        if (aa.upp[naxles][i] == 6) {
          AddToList(edgelist, b, c, aa.upp[naxles]);
          continue;
        }
        d = 3 * deg + i;
        AddToList(edgelist, c, d, aa.upp[naxles]);
        AddToList(edgelist, i, d, aa.upp[naxles]);
        if (aa.upp[naxles][i] == 7) {
          AddToList(edgelist, b, d, aa.upp[naxles]);
          continue;
        }

        Debug.Assert((aa.upp[naxles][i] == 8),
          "Unexpected error in `GetEdgeList'\n");

        e = 4 * deg + i;
        AddToList(edgelist, d, e, aa.upp[naxles]);
        AddToList(edgelist, i, e, aa.upp[naxles]);
        AddToList(edgelist, b, e, aa.upp[naxles]);
      }
    }/* GetEdgeList */

    /**********************************************************************
      AddToList
    See "GetEdgeList" above.
    ***********************************************************************/
    public static void AddToList(
      TpEdgelist edgelist, int u, int v, int[] degree)
    {
      /* adds the pair u,v to edgelist */
      int a, b;

      a = degree[u];
      b = degree[v];
      if ((a >= b) && (b <= 8) && (a <= 11) && ((a <= 8) || (u == 0))) {
        Debug.Assert((edgelist.edg[a][b][0] + 2 < MAXELIST),
          "More than %d entries in edgelist needed\n");
        edgelist.edg[a][b][++edgelist.edg[a][b][0]] = u;
        edgelist.edg[a][b][++edgelist.edg[a][b][0]] = v;
      }
      if ((b >= a) && (a <= 8) && (b <= 11) && ((b <= 8) || (v == 0))) {
        Debug.Assert((edgelist.edg[b][a][0] + 2 < MAXELIST),
          "More than %d entries in edgelist needed\n");
        edgelist.edg[b][a][++edgelist.edg[b][a][0]] = v;
        edgelist.edg[b][a][++edgelist.edg[b][a][0]] = u;
      }
    }

    /**********************************************************************
      RootedSubConf
    See "SubConf" below.
    ***********************************************************************/
    public static bool RootedSubConf(
      int[] degree, TpAdjmat adjmat, TpQuestion question, TpVertices image, bool[] used, int x, int y, int clockwise)
    {
      int deg, j, w;

      deg = degree[0];
      for (j = 0; j < CARTVERT; j++) {
        used[j]      = false;
        image.ver[j] = -1;
      }
      image.ver[0] = clockwise;
      image.ver[question.qc[0]] = x;
      image.ver[question.qc[1]] = y;
      used[x] = true;
      used[y] = true;
      //for (Q = question + 2; Q->u >= 0; Q++) {
      for (j = 2; question.qa[j] >= 0; j++) {
        if (clockwise != 0)
          w = adjmat.adj[image.ver[question.qa[j]]][image.ver[question.qb[j]]];
        else
          w = adjmat.adj[image.ver[question.qb[j]]][image.ver[question.qa[j]]];
        if (w == -1)
          return false;
        if ((question.qd[j] != 0) && question.qd[j] != degree[w])
          return false;
        if (used[w])
          return false;
        image.ver[question.qc[j]] = w;
        used[w] = true;
      }

      /* test if image is well-positioned */
      for (j = 1; j <= deg; j++)
        if (!used[j] && used[deg + j] && used[(j == 1) ? 2 * deg : deg + j - 1])
          return false;

      return true;
    }/* RootedSubConf */

    /**********************************************************************
      SubConf
    Given "adjmat", "degree" and "edgelist" derived from an axle A, and
    "question" for a configuration L it tests using [D, theorem (6.3)]
    if L is a well-positioned induced subconfiguration of the skeleton
    of A. If not returns 0; otherwise returns 1, writes an isomorphism
    into image, and sets image[0] to 1 if the isomorphism is orientation-
    preserving, and 0 if it is orientation-reversing.
    ***********************************************************************/
    public static bool SubConf(
      TpAdjmat adjmat, int[] degree, TpQuestion question, TpEdgelist edgelist, TpVertices image, bool[] used)
    {
      int i, x, y;

      for (i = 1; i <= edgelist.edg[question.qd[0]][question.qd[1]][0]; i++) {
        x = edgelist.edg[question.qd[0]][question.qd[1]][i++];
        y = edgelist.edg[question.qd[0]][question.qd[1]][i];
        if (RootedSubConf(degree, adjmat, question, image, used, x, y, 1) ||
            RootedSubConf(degree, adjmat, question, image, used, x, y, 0))
          return true;
      }
      return false;
    }/* SubConf */

    /*********************************************************************
            GetQuestion
    Computes a question Q=(Q[0],Q[1],...,Q[n]) for L. Moreover, sets
    Q[1].u to be the number of vertices of the free completion of L,
    and Q[1].v to be the ring-size of L. Also sets Q[n+1].u=-1 to
    indicate end
    *********************************************************************/
    public static void GetQuestion(int[][] L, TpQuestion Q) {
      int nverts, max, ring;
      bool[] found = new bool[VERTS];
      int d, g, h, i, j, r, t, u, v, w, best, secondbest, nfound, search;

      nverts = Q.qa[1] = L[0+1][0];
      ring   = Q.qb[1] = L[0+1][1];
      for (v = 0; v <= nverts; v++)
        found[v] = false;
      for (best = 0, max = 0, v = ring + 1; v <= nverts; v++) {
        if (L[v+2][0+1] > max) {
          max = L[v+2][0+1];
          best = v;
          // Console.Write("aaaaaaaaa {0} {1}\n", max, best);
        }
      }
      Q.qc[0] = best;
      Q.qd[0] = L[best+2][0+1];
      found[best] = true;
      for (secondbest = 0, max = 0, i = 1; i <= L[best+2][0+1]; i++) {
        v = L[best+2][i+1];
        if (v <= ring)
          continue;
        if (L[v+2][0+1] > max) {
          max = L[v+2][0+1];
          secondbest = v;
        }
      }
      Q.qc[1] = secondbest;
      Q.qd[1] = L[secondbest+2][0+1];
      found[secondbest] = true;
      nfound = 2;
      for (search = 0; search < nfound; search++) {
        v = Q.qc[search];
        if (v <= ring)
          continue;
        d = L[v+2][0+1];
        for (i = 1; !found[L[v+2][i+1]]; i++);
        for (u = 0, h = (i == 1) ? d : i - 1; h != i; h = (h == 1) ? d : h - 1) {
          u = L[v+2][h+1];
          if (u <= ring)
            break;
          if (found[u])
            continue;
          Q.qc[nfound] = u;
          Q.qd[nfound] = u > ring ? L[u+2][0+1] : 0;
          Q.qa[nfound] = L[v+2][(h == d) ? 1+1 : h + 1+1];
          Q.qb[nfound] = v;
          nfound++;
          found[u] = true;
        }
        if (h == i)
        continue;
        for (j = (i == d) ? 1 : i + 1;; j = (j == d) ? 1 : j + 1) {
          w = L[v+2][j+1];
          if (w <= ring)
            break;
          if (found[w])
            continue;
          Q.qc[nfound] = w;
          Q.qd[nfound] = w > ring ? L[w+2][0+1] : 0;
          Q.qa[nfound] = v;
          Q.qb[nfound] = L[v+2][(j == 1) ? d+1 : j - 1 +1];
          nfound++;
          found[w] = true;
        }
        r = (h >= j) ? h - j : h - j + d;
        if (r <= 2)
          continue;
        Q.qc[nfound] = u;
        Q.qd[nfound] = u > ring ? L[u+2][0+1] : 0;
        Q.qa[nfound] = L[v+2][(h == d) ? 1+1 : h + 1+1];
        Q.qb[nfound] = v;
        nfound++;
        for (g = (h == 1) ? d : h - 1; g != j; g = (g == 1) ? d : g - 1) {
          t = L[v+2][g+1];
          // if ((t <= ring) || (found[t])) {
          //   (void) printf("error in getquestions\n");
          //   exit(1);
          // }
          Q.qc[nfound] = t;
          Q.qd[nfound] = t > ring ? L[t+2][0+1] : 0;
          Q.qa[nfound] = Q.qc[nfound - 1];
          Q.qb[nfound] = v;
          nfound++;
          found[t] = true;
        }
      }
      Q.qa[nfound] = -1;	/* indicates end */
    }/* GetQuestion */

    public static TpQuestion[] ReduceInit(TpReducePack1 rp1in, TpReducePack2 rp2in, int[][][] gConfs)
    {
      int i;
      for (i = 0; i < 633; i++) {
        redquestions[i] = new TpQuestion(new int[VERTS], new int[VERTS], new int[VERTS], new int[VERTS]);
      }
      for (i = 0; i < 633; i++) {
        GetQuestion(gConfs[i], redquestions[i]);
      }
      // シャローコピーなのか？
      rp1 = rp1in;
      rp2 = rp2in;

      return redquestions;
    }

    public static TpReduceRet Reduce(TpAxle axles)
    {
      int h, i, j, v, redring, redverts;
      int naxles, noconf;

      Array.Copy(axles.low[axles.lev], rp1.axle.low[0], CARTVERT);
      Array.Copy(axles.upp[axles.lev], rp1.axle.upp[0], CARTVERT);
      Console.Write("Testing reducibility. Putting input axle on stack.\n");

      noconf = 633;
      for (naxles = 1; naxles > 0 && naxles < MAXASTACK;) {
        --naxles; //CopyAxle(B, rp1[--naxles]);
        Console.Write("Axle from stack:");
        Getadjmat(naxles, rp1.axle, rp1.adjmat);
        GetEdgelist(naxles, rp1.axle, rp2.edgelist);
        for (h = 0; h < noconf; ++h)
          if (SubConf(rp1.adjmat, rp1.axle.upp[naxles], redquestions[h], rp2.edgelist, rp2.image, rp2.used))
            break;
        if (h == noconf) {
          Console.Write("Not reducible\n");
          TpReduceRet retF = new TpReduceRet(false, rp1.axle, rp2.used, rp2.image);
          return retF;
        }
        /* Semi-reducibility test found h-th configuration, say K, appearing */
        redverts = redquestions[h].qa[1];
        redring  = redquestions[h].qb[1];
        /* the above are no vertices and ring-size of free completion of K */
        /* could not use conf[h][0][0], because conf may be NULL           */

        Console.Write("Conf({0},{1},{2}): ", h / 70 + 1, (h % 70) / 7 + 1, h % 7 + 1);
        for (j = 1; j <= redverts; j++) {
          if (rp2.image.ver[j] != -1)
              Console.Write(" {0}({1})", rp2.image.ver[j], j);
        }
        Console.Write("\n");
        //if (conf != NULL)
        //  CheckIso(conf[h], B, image, lineno);
        /* Double-check isomorphism */

        for (i = redring + 1; i <= redverts; i++) {
          v = rp2.image.ver[i];
          if (rp1.axle.low[naxles][v] == rp1.axle.upp[naxles][v])
            continue;
          Console.Write("Lowering upper bound of vertex ");
          Console.Write("{0} to {1} and adding to stack\n", v, rp1.axle.upp[naxles][v] - 1);

          Debug.Assert((naxles < MAXASTACK),
            "More than %d elements in axle stack needed\n");

          // コピー
          if (naxles != 0) {
            Array.Copy(rp1.axle.low[naxles - 1], rp1.axle.low[naxles], CARTVERT);
            Array.Copy(rp1.axle.upp[naxles - 1], rp1.axle.upp[naxles], CARTVERT);
          }
          // デクリメント
          rp1.axle.upp[naxles][v]--;
          // インクリメント
          naxles++;
        }

      }//naxles

      Console.Write("All possibilities for lower degrees tested\n");
      TpReduceRet retT = new TpReduceRet(true, rp1.axle, rp2.used, rp2.image);
      return retT;

    }
  }
}



