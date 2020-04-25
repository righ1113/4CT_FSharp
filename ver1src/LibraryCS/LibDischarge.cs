using System;
using System.Diagnostics;
using LibraryFS;


namespace LibraryCS2 {
  public static class LibDischarge {
  }
  public static class LibDischargeSymmetry {
    public static int DelSym(
      int nosym, int[] nolines, int lev)
    {

      for (; nosym >= 1 && nolines[nosym - 1] - 1 >= lev; nosym--)
      /* do nothing */ ;

      return nosym;
    }

    /*********************************************************************
                OutletForced
    If (T,x) is enforced by A, then returns the value of T, otherwise 0
    *********************************************************************/
    public static int OutletForced(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI)
    {
      int i, p, deg;

      deg = lowI[0];
      xxI--;
      for (i = 0; i < nolinesI; ++i) {
        p = posI[i];
        p = xxI + (p - 1) % deg < deg ? p + xxI : p + xxI - deg;
        if (p >= puppI.Length){ p = puppI.Length - 1; }
        if (plowI[i] > lowI[p] || puppI[i] < uppI[p])
          return 0;
      }
      return valueI;
    }

    /*********************************************************************
                OutletPermitted
    If (T,x) is permitted by A, then returns the value of T, otherwise 0
    *********************************************************************/
    public static int OutletPermitted(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI)
    {
      int deg, i, p;

      deg = lowI[0];
      xxI--;
      for (i = 0; i < nolinesI; ++i) {
        p = posI[i];
        p = xxI + (p - 1) % deg < deg ? p + xxI : p + xxI - deg;
        if (plowI[i] > uppI[p] || puppI[i] < lowI[p])
          return 0;
      }	/* i */
      return valueI;
    }/* OutletPermitted */

    /************************************************************************
                ReflForced
    Returns the value of T if M is fan-free and every cartwheel compatible
    with A is compatible with tau^(x-1)sigma M, where M is the axle
    corresponding to T
    ************************************************************************/
    public static int ReflForced(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI)
    {
      int deg, i, p, q;

      deg = lowI[0];
      xxI--;
      for (i = 0; i < nolinesI; ++i) {
        p = posI[i];
        p = xxI + (p - 1) % deg < deg ? p + xxI : p + xxI - deg;
        if (p < 1 || p > 2 * deg)
          return 0;
        else if (p <= deg)
          q = deg - p + 1;
        else if (p < 2 * deg)
          q = 3 * deg - p;
        else
          q = 2 * deg;
        if (plowI[i] > lowI[q] || puppI[i] < uppI[q])
          return 0;
      }
      return valueI;
    }
  }

  public static class LibDischargeHubcap {
    /*************************************************************************
        CheckBound
    Verifies (H1)
    *************************************************************************/
    public static bool CheckBound(
      LibFS.TpPosout posout, int[] s, int maxch, int pos, int depth, ref LibFS.TpReducePack1 rP1, ref LibFS.TpReducePack2 rP2, LibFS.TpAxle axles)
    {
      int deg, i, x, good, forcedch, allowedch;
      int[] sprime = new int[2 * 110 + 1];
      int p;
      int retN;
      LibFS.TpReduceRet ret;

      int j;
      int[][] cpLow = new int[12 + 1][];
      for (j = 0; j < 13; j++) {
        cpLow[j] = new int[5 * 12 + 2];
      }
      int[][] cpUpp = new int[12 + 1][];
      for (j = 0; j < 13; j++) {
        cpUpp[j] = new int[5 * 12 + 2];
      }

      deg = axles.low[axles.lev][0];

      // 1. compute forced and permitted rules, allowedch, forcedch, update s
      forcedch = allowedch = 0;
      for (i = 0; s[i] < 99; i++) {
        if (s[i] > 0)
          forcedch += posout.value[i];
        if (s[i] != 0)
          continue;
        retN = LibDischargeSymmetry.OutletForced(axles.low[axles.lev],
                                                 axles.upp[axles.lev],
                                                 posout.number[i],
                                                 posout.nolines[i],
                                                 posout.value[i],
                                                 posout.pos[i],
                                                 posout.plow[i],
                                                 posout.pupp[i],
                                                 posout.xx[i]);
        if (retN != 0) {
          s[i] = 1;
          forcedch += posout.value[i];
        }
        else if (LibDischargeSymmetry.OutletPermitted(axles.low[axles.lev],
                                                      axles.upp[axles.lev],
                                                      posout.number[i],
                                                      posout.nolines[i],
                                                      posout.value[i],
                                                      posout.pos[i],
                                                      posout.plow[i],
                                                      posout.pupp[i],
                                                      posout.xx[i]) == 0) {
          s[i] = -1;
        }
        else if (posout.value[i] > 0) {
          allowedch += posout.value[i];
        }
      }

      // 2.
      Console.Write("{0} POs: ", depth);
      for (i = 0; s[i] < 99; i++) {
        if (s[i] < 0)
          continue;
        if (s[i] == 0)
          Console.Write("?");
        Console.Write("{0},{1} ", posout.number[i], posout.xx[i]);
      }
      Console.Write("\n");

      // 3. check if inequality holds
      if (forcedch + allowedch <= maxch) {
        Console.Write("{0} Inequality holds. Case done.\n", depth);
        return true;
      }

      // 4. check reducibility
      if (forcedch > maxch) {
        ret = LibDischargeReduce.Reduce(ref rP1, ref rP2, axles);
        if (ret.retB == false) {
          Console.Write("ihihi\n");
        }
        Debug.Assert(ret.retB,
          "Incorrect hubcap upper bound");
        Console.Write("{0} {1} {2} Reducible. Case done.\n", forcedch, allowedch, maxch);
        return true;
      }

      // 5.
      //for (PO = posout + pos; s[pos] < 99; pos++, PO++) {
      for (; s[pos] < 99; pos++) {
        if (s[pos] != 0 || posout.value[pos] < 0)
          continue;
        x = posout.xx[pos];

        // accepting positioned outlet PO, computing AA
        for (j = 0; j < 13; j++) {
          Array.Copy(axles.low[j], cpLow[j], axles.low[j].Length);
          Array.Copy(axles.upp[j], cpUpp[j], axles.upp[j].Length);
        }
        LibFS.TpAxle axles2 = new LibFS.TpAxle(cpLow, cpUpp, axles.lev);
        for (i = 0; i < posout.nolines[pos]; ++i) {
          if (pos > 219) break;
          p = posout.pos[pos][i];
          p = x - 1 + (p - 1) % deg < deg ? p + x - 1 : p + x - 1 - deg;
          if (p >= 62) break;
          if (posout.plow[pos][i] > axles2.low[axles2.lev][p])
            axles2.low[axles2.lev][p] = posout.plow[pos][i];
          if (posout.pupp[pos][i] < axles2.upp[axles2.lev][p])
            axles2.upp[axles2.lev][p] = posout.pupp[pos][i];
          Debug.Assert((axles2.low[axles2.lev][p] <= axles2.upp[axles2.lev][p]),
            "Unexpected error 321");
        }

        // Check if a previously rejected positioned outlet is forced to apply
        good = 1;
        for (i = 0; i < pos; i++) {
          if (s[i] == -1
              && LibDischargeSymmetry.OutletForced(axles2.low[axles2.lev],
                                                   axles2.upp[axles2.lev],
                                                   posout.number[i],
                                                   posout.nolines[i],
                                                   posout.value[i],
                                                   posout.pos[i],
                                                   posout.plow[i],
                                                   posout.pupp[i],
                                                   posout.xx[i]) != 0) {
            Console.Write("{0} Positioned outlet ", depth);
            Console.Write("{0},{1} can't be forced, because it forces {2},{3}\n", posout.number[pos], x, posout.number[i], posout.xx[i]);
            good = 0;
            break;
          }
        }
        if (good != 0) {
          // recursion with PO forced
          for (i = 0; (sprime[i] = s[i]) < 99; ++i)	// do nothing
            ;
          sprime[pos] = 1;
          Console.Write("{0} Starting recursion with ", depth);
          Console.Write("{0},{1} forced\n", posout.number[pos], x);
          CheckBound(posout, sprime, maxch, pos + 1, depth + 1, ref rP1, ref rP2, axles2);
        }

        // rejecting positioned outlet PO
        Console.Write("{0} Rejecting positioned outlet ", depth);
        Console.Write("{0},{1}. ", posout.number[pos], x);
        s[pos] = -1;
        allowedch -= posout.value[pos];
        if (allowedch + forcedch <= maxch) {
          Console.Write("Inequality holds.\n");
          return true;
        } else {
          Console.Write("\n");
        }
      }// pos

      // 6.
      Debug.Assert(false,
        "Unexpected error 101");
      return false;

    }// CheckBound
  }

  public static class LibDischargeReduce {
    public const int CARTVERT    = 5 * 12 + 2;     // domain of l_A, u_A, where A is an axle
    public const int MAXELIST    = 134;            // length of edgelist[a][b]
    public const int MAXASTACK   = 5;              // max height of Astack (see "Reduce")

    /*********************************************************************
      Getadjmat
    Computes adjmat defined as follows. Let G=G(L), where L is the
    skeleton of A. Notice that G only depends on u_B(i) for i=0,1,..,deg.
    Then adjmat[u][v]=w if u,v,w form a clockwise triangle in G, and
    adjmat[u][v]=-1 if w does not exist.
    *********************************************************************/
    public static void Getadjmat(int naxles, LibFS.TpAxle aa, LibFS.TpAdjmat adjmat)
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
    public static void DoFan(int deg, int i, int k, LibFS.TpAdjmat adjmat)
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
      int naxles, LibFS.TpAxle aa, LibFS.TpEdgelist edgelist)
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
      LibFS.TpEdgelist edgelist, int u, int v, int[] degree)
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
      int[] degree, LibFS.TpAdjmat adjmat, LibFS.TpQuestion question, LibFS.TpVertices image, bool[] used, int x, int y, int clockwise)
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
      used[y] = false;
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
      LibFS.TpAdjmat adjmat, int[] degree, LibFS.TpQuestion question, LibFS.TpEdgelist edgelist, LibFS.TpVertices image, bool[] used)
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

    public static LibFS.TpReduceRet Reduce(
      ref LibFS.TpReducePack1 rP1, ref LibFS.TpReducePack2 rP2, LibFS.TpAxle axles)
    {
      rP1.axle.low[0] = axles.low[axles.lev];
      rP1.axle.upp[0] = axles.upp[axles.lev];
      return ReduceSub(ref rP1, ref rP2);
    }

    public static LibFS.TpReduceRet ReduceSub(
      ref LibFS.TpReducePack1 aStack, ref LibFS.TpReducePack2 rP2)
    {
      int h, i, j, v, redring, redverts;
      int naxles, noconf;

      Console.Write("Testing reducibility. Putting input axle on stack.\n");

      noconf = 633;
      for (naxles = 1; naxles > 0 && naxles < MAXASTACK;) {
        --naxles; //CopyAxle(B, Astack[--naxles]);
        Console.Write("Axle from stack:");
        Getadjmat(naxles, aStack.axle, aStack.adjmat);
        GetEdgelist(naxles, aStack.axle, rP2.edgelist);
        for (h = 0; h < noconf; ++h)
          if (SubConf(aStack.adjmat, aStack.axle.upp[naxles], rP2.redquestions[h], rP2.edgelist, rP2.image, rP2.used))
            break;
        if (h == noconf) {
          Console.Write("Not reducible\n");
          LibFS.TpReduceRet retF = new LibFS.TpReduceRet(false, aStack.axle, rP2.used, rP2.image);
          return retF;
        }
        /* Semi-reducibility test found h-th configuration, say K, appearing */
        redverts = rP2.redquestions[h].qa[1];
        redring  = rP2.redquestions[h].qb[1];
        /* the above are no vertices and ring-size of free completion of K */
        /* could not use conf[h][0][0], because conf may be NULL           */

        Console.Write("Conf({0},{1},{2}): ", h / 70 + 1, (h % 70) / 7 + 1, h % 7 + 1);
        for (j = 1; j <= redverts; j++) {
          if (rP2.image.ver[j] != -1)
              Console.Write(" {0}({1})", rP2.image.ver[j], j);
        }
        Console.Write("\n");
        //if (conf != NULL)
        //  CheckIso(conf[h], B, image, lineno);
        /* Double-check isomorphism */

        for (i = redring + 1; i <= redverts; i++) {
          v = rP2.image.ver[i];
          if (aStack.axle.low[naxles][v] == aStack.axle.upp[naxles][v])
            continue;
          Console.Write("Lowering upper bound of vertex ");
          Console.Write("{0} to {1} and adding to stack\n", v, aStack.axle.upp[naxles][v] - 1);

          Debug.Assert((naxles < MAXASTACK),
            "More than %d elements in axle stack needed\n");

          aStack.axle.upp[naxles][v]--;
          naxles++;
        }

      }//naxles

      Console.Write("All possibilities for lower degrees tested\n");
      LibFS.TpReduceRet retT = new LibFS.TpReduceRet(true,  aStack.axle, rP2.used, rP2.image);
      return retT;

    }
  }

}



