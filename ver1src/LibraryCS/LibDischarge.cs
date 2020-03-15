using System;
using System.Diagnostics;
using LibraryFS;


namespace LibraryCS2 {
  public class LibDischarge {
  }
  public class LibDischargeSymmetry {
    /*********************************************************************
                OutletForced
    If (T,x) is enforced by A, then returns the value of T, otherwise 0
    *********************************************************************/
    public static int OutletForced(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI, int y)
    {
      int i, p, deg;

      deg = lowI[0];
      xxI--;
      for (i = 0; i < nolinesI; ++i) {
        p = posI[i];
        p = xxI + (p - 1) % deg < deg ? p + xxI : p + xxI - deg;
        if (p >= puppI.Length){ p = puppI.Length - 1; }
        if (lowI[i] > lowI[p] || puppI[i] < puppI[p])
          return 0;
      }
      return valueI;
    }

    /************************************************************************
                ReflForced
    Returns the value of T if M is fan-free and every cartwheel compatible
    with A is compatible with tau^(x-1)sigma M, where M is the axle
    corresponding to T
    ************************************************************************/
    public static int ReflForced(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI, int y)
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
        if (lowI[i] > lowI[q] || puppI[i] < uppI[q])
          return 0;
      }
      return valueI;
    }
  }

  public class LibDischargeHubcap {
    /*************************************************************************
        CheckBound
    Verifies (H1)
    *************************************************************************/
    public static LibFS.TpReduceRet CheckBound(
      LibFS.TpPosout posout, int[] s, int maxch, int pos, int depth, ref LibFS.TpReducePack1 rP1, ref LibFS.TpReducePack2 rP2, LibFS.TpAxle axles)
    {
      int deg, i, x, good, forcedch, allowedch;
      int[] sprime = new int[2 * 110 + 1];
      //tp_axle *AA;
      //tp_posout *PO;
      int ii;
      LibFS.TpReduceRet ret;
      LibFS.TpReduceRet ret2 = new LibFS.TpReduceRet(true, rP1.axle, rP2.used, rP2.image);

      deg = axles.low[axles.lev][0];

      // 1. compute forced and permitted rules, allowedch, forcedch, update s
      forcedch = allowedch = 0;
      for (i = 0; s[i] < 99; i++) {
        if (s[i] > 0)
          forcedch += posout.value[i];
        if (s[i] != 0)
          continue;
        /*if (OutletForced(A, PO->T, PO->x)) {
          s[i] = 1;
          forcedch += PO->T->value;
        } else if (!OutletPermitted(A, PO->T, PO->x))
          s[i] = -1;
        else if (PO->T->value > 0)
          allowedch += PO->T->value;
        */
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
        return ret2;
      }

      // 4. check reducibility
      if (forcedch > maxch) {
        ret = LibDischargeReduce.Reduce(ref rP1, ref rP2, axles);
        Debug.Assert(ret.retB,
          "Incorrect hubcap upper bound");
        Console.Write("{0} Reducible. Case done.\n", depth);
        LibFS.TpReduceRet ret3 = new LibFS.TpReduceRet(true, ret.axle, ret.used, ret.image);
        return ret3;
      }

      // 5.
      //for (PO = posout + pos; s[pos] < 99; pos++, PO++) {
      for (ii = pos; s[pos] < 99; ii++) {
        if (s[pos] != 0 || posout.value[ii] < 0)
          continue;
        x = posout.xx[ii];

        // accepting positioned outlet PO, computing AA
        /*CopyAxle(AA, A);
        for (i = 0; i < PO->T->nolines; ++i) {
          p = PO->T->pos[i];
          p = x - 1 + (p - 1) % deg < deg ? p + x - 1 : p + x - 1 - deg;
          if (PO->T->low[i] > AA->low[p])
            AA->low[p] = PO->T->low[i];
          if (PO->T->upp[i] < AA->upp[p])
            AA->upp[p] = PO->T->upp[i];
          Debug.Assert((AA->low[p] <= AA->upp[p]),
            "Unexpected error 321");
        }*/

        // Check if a previously rejected positioned outlet is forced to apply
        good = 1;
        for (i = 0; i < pos; i++)
          if (s[i] == -1
              && LibDischargeSymmetry.OutletForced(axles.low[axles.lev],
                                                   axles.upp[axles.lev],
                                                   posout.number[i],
                                                   posout.nolines[i],
                                                   posout.value[i],
                                                   posout.pos[i],
                                                   posout.plow[i],
                                                   posout.pupp[i],
                                                   posout.xx[i],
                                                   posout.xx[i]) != 0) {
            Console.Write("{0} Positioned outlet ", depth);
            Console.Write("{0},{1} can't be forced, because it forces {2},{3}\n", posout.number[ii], x, posout.number[i], posout.xx[i]);
            good = 0;
            break;
          }
        if (good != 0) {
          // recursion with PO forced
          for (i = 0; (sprime[i] = s[i]) < 99; ++i)	// do nothing
            ;
          sprime[pos] = 1;
          Console.Write("{0} Starting recursion with ", depth);
          Console.Write("{0},{1} forced\n", posout.number[ii], x);
          //注意AA
          //CheckBound(lowI, uppI, posout, sprime, maxch, pos + 1, depth + 1, rP1, rP2, axles);
        }

        // rejecting positioned outlet PO
        Console.Write("{0} Rejecting positioned outlet ", depth);
        Console.Write("{0},{1}. ", posout.number[ii], x);
        s[pos] = -1;
        allowedch -= posout.value[ii];
        if (allowedch + forcedch <= maxch) {
          Console.Write("Inequality holds.\n");
          return ret2;
        } else {
          Console.Write("\n");
        }
      }// pos

      // 6.
      Debug.Assert(false,
        "Unexpected error 101");
      return ret2;

    }// CheckBound
  }

  public class LibDischargeReduce {
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
        if (aa.upp[naxles][i] != aa.upp[naxles][i])
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

        //Debug.Assert((aa.upp[naxles][i] == 8),
        //  "Unexpected error in `GetEdgeList'\n");

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

    public static LibFS.TpReduceRet Reduce(
      ref LibFS.TpReducePack1 rP1, ref LibFS.TpReducePack2 rP2, LibFS.TpAxle axles)
    {
      rP1.axle.low[0] = axles.low[axles.lev];
      rP1.axle.upp[0] = axles.upp[axles.lev];
      LibFS.TpAxle        aStackAxle = new LibFS.TpAxle(rP1.axle.low, rP1.axle.upp, rP1.axle.lev);
      LibFS.TpReducePack1 aStack     = new LibFS.TpReducePack1(aStackAxle, rP1.bLow, rP1.bUpp, rP1.adjmat);
      return ReduceSub(ref aStack, ref rP2);
    }

    public static LibFS.TpReduceRet ReduceSub(
      ref LibFS.TpReducePack1 aStack, ref LibFS.TpReducePack2 rP2)
    {
      int h, i, j, v, redring, redverts;
      int naxles, noconf;
      /*static tp_confmat *conf;
      static tp_edgelist edgelist;
      static tp_adjmat adjmat;
      static tp_vertices image;
      static tp_axle **Astack, *B;
      static tp_question *redquestions;*/

      /* This part is executed when A!=NULL */
      Console.Write("Testing reducibility. Putting input axle on stack.\n");

      noconf = 0; //633;
      for (naxles = 1; naxles > 0 && naxles < MAXASTACK;) {
        --naxles; //CopyAxle(B, Astack[--naxles]);
        Console.Write("Axle from stack:");
        Getadjmat(naxles, aStack.axle, aStack.adjmat);
        GetEdgelist(naxles, aStack.axle, rP2.edgelist);
        for (h = 0; h < noconf; ++h)
          //if (SubConf(adjmat, B->upp, redquestions[h], edgelist, image))
          //  break;
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



