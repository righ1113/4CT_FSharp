using System;
using System.Diagnostics;

namespace LibraryCS2 {
  public class LibDischarge {
  }
  public class LibDischargeSymmetry {
    public static int OutletForced(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI, int y)
    {
      /*********************************************************************
                  OutletForced
      If (T,x) is enforced by A, then returns the value of T, otherwise 0
      *********************************************************************/
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
    public static int ReflForced(
      int[] lowI, int[] uppI, int numberI, int nolinesI, int valueI, int[] posI, int[] plowI, int[] puppI, int xxI, int y)
    {
      /************************************************************************
                  ReflForced
      Returns the value of T if M is fan-free and every cartwheel compatible
      with A is compatible with tau^(x-1)sigma M, where M is the axle
      corresponding to T
      ************************************************************************/
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
}



