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
      LibFS.TpPosout posout, int[] s, int maxch, int pos, int depth, LibFS.TpReducePack1 rP1, LibFS.TpReducePack2 rP2, LibFS.TpAxle axles)
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
        ret = LibDischargeReduce.Reduce(rP1, rP2, axles);
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
    public static LibFS.TpReduceRet Reduce(
      LibFS.TpReducePack1 rP1, LibFS.TpReducePack2 rP2, LibFS.TpAxle axles)
    {
      LibFS.TpReduceRet ret = new LibFS.TpReduceRet(true, rP1.axle, rP2.used, rP2.image);
      return ret;
    }
  }

}



