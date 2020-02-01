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
    public static void CheckBound(
      int[] lowI, int[] uppI, LibFS.TpPosout posout, int[] s, int maxch, int pos, int depth)
    {
      int deg, i, p, x, good, forcedch, allowedch;
      //int *sprime;
      //tp_axle *AA;
      //tp_posout *PO;

      deg = lowI[0];
/*
      // compute forced and permitted rules, allowedch, forcedch, update s
      forcedch = allowedch = 0;
      for (i = 0, PO = posout; s[i] < 99; i++, PO++) {
        if (s[i] > 0)
          forcedch += PO->T->value;
        if (s[i])
          continue;
        if (OutletForced(A, PO->T, PO->x)) {
          s[i] = 1;
          forcedch += PO->T->value;
        } else if (!OutletPermitted(A, PO->T, PO->x))
          s[i] = -1;
        else if (PO->T->value > 0)
          allowedch += PO->T->value;
      }

      if (print >= PRTPAI) {
        Indent(depth, "POs: ");
        for (i = 0, PO = posout; s[i] < 99; i++, PO++) {
          if (s[i] < 0)
            continue;
          if (s[i] == 0)
            (void) printf("?");
          (void) printf("%d,%d ", PO->T->number, PO->x);
        }
        (void) printf("\n");
      }
      // check if inequality holds
      if (forcedch + allowedch <= maxch) {
        if (print >= PRTPAI)
        Indent(depth, "Inequality holds. Case done.\n");
        return;
      }
      // check reducibility
      if (forcedch > maxch) {
        if (Reduce(A, lineno, print >= PRTALL ? 1 : 0) != 1)
          Error("Incorrect hubcap upper bound", lineno);
        if (print >= PRTPAI && print < PRTALL)
          Indent(depth, "Reducible. Case done.\n");
        return;
      }
      ALLOC(sprime, 2 * MAXOUTLETS + 1, int);
      ALLOC(AA, 1, tp_axle);

      for (PO = posout + pos; s[pos] < 99; pos++, PO++) {
        if (s[pos] || PO->T->value < 0)
          continue;
        x = PO->x;

        // accepting positioned outlet PO, computing AA
        CopyAxle(AA, A);
        for (i = 0; i < PO->T->nolines; ++i) {
          p = PO->T->pos[i];
          p = x - 1 + (p - 1) % deg < deg ? p + x - 1 : p + x - 1 - deg;
          if (PO->T->low[i] > AA->low[p])
            AA->low[p] = PO->T->low[i];
          if (PO->T->upp[i] < AA->upp[p])
            AA->upp[p] = PO->T->upp[i];
          if (AA->low[p] > AA->upp[p])
            Error("Unexpected error 321", lineno);
        }

        // Check if a previously rejected positioned outlet is forced to apply
        good = 1;
        for (i = 0; i < pos; i++)
          if (s[i] == -1 && OutletForced(AA, posout[i].T, posout[i].x)) {
            if (print >= PRTPAI) {
              Indent(depth, "Positioned outlet ");
              (void) printf("%d,%d can't be forced, because it forces %d,%d\n", PO->T->number, x, posout[i].T->number, posout[i].x);
            }
            good = 0;
            break;
          }

        if (good) {
          // recursion with PO forced
          for (i = 0; (sprime[i] = s[i]) < 99; ++i)	// do nothing
            ;
          sprime[pos] = 1;
          if (print >= PRTPAI) {
            Indent(depth, "Starting recursion with ");
            (void) printf("%d,%d forced\n", PO->T->number, x);
          }
          CheckBound(AA, posout, sprime, maxch, pos + 1, depth + 1, lineno, print);
        }

        // rejecting positioned outlet PO
        if (print >= PRTPAI) {
          Indent(depth, "Rejecting positioned outlet ");
          (void) printf("%d,%d. ", PO->T->number, x);
        }
        s[pos] = -1;
        allowedch -= PO->T->value;
        if (allowedch + forcedch <= maxch) {
          if (print >= PRTPAI)
            (void) printf("Inequality holds.\n");
          free(sprime);
          free(AA);
          return;
        } else if (print >= PRTPAI)
          (void) printf("\n");
      }	// pos
      Error("Unexpected error 101", lineno);
*/
    }// CheckBound
  }

}



