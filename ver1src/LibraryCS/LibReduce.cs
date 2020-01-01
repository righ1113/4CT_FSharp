using System;
using System.Diagnostics;

namespace LibraryCS {
  public class LibReduce {
  }
  public class LibReduceStrip {
    /* if grav meets the done vertices in an interval of length >=1, it returns
    * the length of the interval, and otherwise returns 0 */
    public static int Ininterval(int[] grav, bool[] done) {
      int d, j, first, last, length;
      bool worried;

      d = grav[0 + 1];
      for (first = 1; (first < d) && (!done[grav[first + 1]]); first++);
      if (first == d)
        return done[grav[d + 1]] ? 1 : 0;
      for (last = first; (last < d) && (done[grav[1 + last + 1]]); last++);
      length = last - first + 1;
      if (last == d)
        return length;
      if (first > 1) {
        for (j = last + 2; j <= d; j++)
          if (done[grav[j + 1]])
            return 0;
        return length;
      }
      worried = false;
      for (j = last + 2; j <= d; j++) {
        if (done[grav[j + 1]]) {
          length++;
          worried = true;
        } else if (worried)
          return 0;
      }
      return length;
    }
    public static int StripSub2(int MVERTS, int[][] graph, int verts, int ring, int[][] edgeno, bool[] done, int term) {
      int x, maxint, maxes, v, inter, maxdeg;
      int h, best=1, d, first;
      int[] max = new int[MVERTS];
      bool previous;

      for (x = ring + 1; x <= verts; x++) {
        /* First we find all vertices from the interior that meet the "done"
        * vertices in an interval, and write them in max[1] .. max[maxes] */
        maxint = 0;
        maxes = 0;

        for (v = ring + 1; v <= verts; v++) {
          if (done[v])
            continue;
          inter = Ininterval(graph[v + 1], done);
          if (inter > maxint) {
            maxint = inter;
            maxes = 1;
            max[1] = v;
          } else if (inter == maxint)
            max[++maxes] = v;
        }	/* for v bracket */

        /* From the terms in max we choose the one of maximum degree */
        maxdeg = 0;
        for (h = 1; h <= maxes; h++) {
          d = graph[max[h] + 1][0];
          if (d > maxdeg) {
              maxdeg = d;
              best = max[h];
          }
        }
        /* So now, the vertex "best" will be the next vertex to be done */

        d = graph[best + 1][0 + 1];
        first = 1;
        previous = done[graph[best + 1][d + 1]];

        while ((previous) || (!done[graph[best + 1][first + 1]])) {
          previous = done[graph[best + 1][1 + first++]];
          if (first > d) {
            first = 1;
            break;
          }
        }

        for (h = first; done[graph[best + 1][h + 1]]; h++) {
          edgeno[best][graph[best + 1][h + 1]] = term;
          edgeno[graph[best + 1][h + 1]][best] = term;
          term--;
          if (h == d) {
            if (first == 1)
                break;
            h = 0;
          }
        }
        done[best] = true;
      }	/* for x bracket */
      /* This eventually lists all the internal edges of the configuration */

      return term;
    }
  }
  public class LibReduceAngle {
    public static void FindanglesSub2(
      int[][] graph, int[][] edgeno, int[] contract, int[][] angle, int[][] diffangle, int[][] sameangle)
    {
      int v, h, i, u, w, a, b, c;
      int d, e=0;

      for (v = 1; v <= graph[0+1][0]; v++) {
        for (h = 1; h <= graph[v+2][0]; h++) {

          if ((v <= graph[0+1][1]) && (h == graph[v+2][0]))
            continue;
          if (h >= graph[v+2].Length)
            break;

          i = (h < graph[v+2].Length - 1) ? h + 1 : 1;
          u = graph[v+2][h];
          w = graph[v+2][i];
          a = edgeno[v][w+1];
          b = edgeno[u][w+1];
          c = edgeno[u][v+1];

          // どっちかが0なら通過
          //Debug.Assert((contract[a]==0 || contract[b]==0),
          //  "         ***  ERROR: CONTRACT IS NOT SPARSE  ***\n\n");

          if (a > c) {
            d = (angle[c][0] >= 4) ? 4 : ++angle[c][0];
            angle[c][d] = a;
            if ((contract[a] != 0) && (contract[b] != 0) && (contract[c] != 0))
              e = (diffangle[c][0] >= 4) ? 4 : ++diffangle[c][0];
              diffangle[c][e] = a;
            if (contract[b] != 0)
              e = (sameangle[c][0] >= 4) ? 4 : ++sameangle[c][0];
              sameangle[c][e] = a;
          }
          if (b > c) {
            d = (angle[c][0] >= 4) ? 4 : ++angle[c][0];
            angle[c][d] = b;
            if ((contract[a] != 0) && (contract[b] != 0) && (contract[c] != 0))
              e = (diffangle[c][0] >= 4) ? 4 : ++diffangle[c][0];
              diffangle[c][e] = b;
            if (contract[a] != 0)
              e = (sameangle[c][0] >= 4) ? 4 : ++sameangle[c][0];
              sameangle[c][e] = b;
          }
        }
      }

    }
    public static void FindanglesSub3(int MVERTS, int[][] graph, int[] contract)
    {
      int v, i, j, u, a;
      bool[] neighbour = new bool[MVERTS];

      /* checking that there is a triad */
      if (contract[0] < 4)
        return;

      for (v = graph[0+1][1] + 1; v <= graph[0+1][0]; v++) {
        /* v is a candidate triad */
        for (a = 0, i = 1; i <= graph[v+2][0]; i++) {
          u = graph[v+1][i];
          for (j = 5; j <= 12; j++)
            if (u == graph[0+1][j]) {
                a++;
                break;
            }
        }

        if (a < 3)
          continue;
        if (graph[v+2][0] >= 6)
          return;

        for (u = 1; u <= graph[0+1][0]; u++)
          neighbour[u] = false;
        for (i = 1; i <= graph[v+2][0]; i++)
          neighbour[graph[v+2][i]] = true;
        for (j = 5; j <= 12; j++) {
          if (!neighbour[graph[0+1][j]])
            return;
        }
      }

      Debug.Assert(false,
        "         ***  ERROR: CONTRACT HAS NO TRIAD  ***\n\n");
    }
  }
  public class LibReduceLive {
    public static int[] simatchnumber = new int[] {0, 0, 1, 3, 10, 30, 95, 301, 980, 3228, 10797, 36487, 124542, 428506, 1485003};
    public static void Printstatus(
      int ring, int totalcols, int extent, int extentclaim)
    {
      Console.Write("\n\n   This has ring-size {0}, so there are {1} colourings total,\n", ring, totalcols);
      Console.Write("   and {0} balanced signed matchings.\n", simatchnumber[ring]);

      Console.Write("\n   There are {0} colourings that extend to the configuration.", extent);

      //Debug.Assert((extent == extentclaim),
      //  "\n   *** ERROR: DISCREPANCY IN NUMBER OF EXTENDING COLOURINGS ***\n");

      Console.Write("\n\n            remaining               remaining balanced\n");
      Console.Write("           colourings               signed matchings\n");
      Console.Write("\n              {0}", totalcols - extent);
    }
    public static int Record(
      int[] col, int[] power, int ring, int[][] angle, int[] live, int extent, int bigno)
    {
      /* Given a colouring specified by a 1,2,4-valued function "col", it computes
      * the corresponding number, checks if it is in live, and if so removes it. */

      int[] weight = new int[5];
      int colno, sum, i, min, max, w;

      for (i = 1; i < 5; i++)
        weight[i] = 0;
      for (i = 1; i <= ring; i++) {
        sum = 7 - col[angle[i][1]] - col[angle[i][2]];
        sum = (sum >= 5) ? 4 : sum;
        weight[sum] += power[i];
      }
      min = max = weight[4];
      for (i = 1; i <= 2; i++) {
        w = weight[i];
        if (w < min)
          min = w;
        else if (w > max)
          max = w;
      }
      colno = bigno - 2 * min - max;
      if (live[colno] != 0) {
        extent++;
        live[colno] = 0;
      }

      return extent;
    }
    public static (int, int[]) FindliveSub(
      int bigno, int[][] angle, int[] power, int ring, int ed, int extentclaim, int ncodes, int[] live, int j, int[] c, int[] forbidden)
    {
      int x, extent=0, u, i;

      for (x = 0; x < 1024; x++) {

        while ((forbidden[j] & c[j]) != 0) {
          c[j] <<= 1;
          while ((c[j] & 8) != 0) {
            if (j >= ed - 1) {
                Printstatus(ring, ncodes, extent, extentclaim);
                return ((ncodes - extent), live);
            }
            c[++j] <<= 1;
          }
        }

        if (j == ring + 1) {
          extent = Record(c, power, ring, angle, live, extent, bigno);
          c[j] <<= 1;
          while ((c[j] & 8) != 0) {
            if (j >= ed - 1) {
                Printstatus(ring, ncodes, extent, extentclaim);
                return ((ncodes - extent), live);
            }
            c[++j] <<= 1;
          }
        }
        else {
          --j;
          if (j < 0) {
              return ((ncodes - extent), live);
          }
          c[j] = 1;
          for (u = 0, i = 1; i <= angle[j][0]; i++)
            u |= c[angle[j][i]];
          forbidden[j] = u;
        }
      }

      Debug.Assert(false,
        "FindliveSub : It was not good though it was repeated 1024 times!");
      return (-1, live);
    }
  }
  public class LibReduceUpdate {
    public static bool Stillreal(
      int col, int[] choice, int depth, int[] live, int on)
    {
      /* Given a signed matching, this checks if all associated colourings are in
      * "live", and, if so, records that fact on the bits of the corresponding
      * entries of "live". */
      int mark, i, j, twopower, b, c;
      int ntwisted, nuntwisted;
      int[] sum       = new int[64];
      int[] twisted   = new int[64];
      int[] untwisted = new int[8];

      ntwisted = nuntwisted = 0;
      if (col < 0) {
        if (live[-col] == 0)
          return false;
        twisted[ntwisted++] = -col;
        sum[0] = col;
      } else {
        if (live[col] == 0)
          return false;
        untwisted[nuntwisted++] = sum[0] = col;
      }
      for (i = 2, twopower = 1, mark = 1; i <= depth; i++, twopower <<= 1) {
        c = choice[i];
        for (j = 0; j < twopower; j++, mark++) {
          b = sum[j] - c;
          if (b < 0) {
            if (live[-b] == 0)
                return false;
            twisted[ntwisted++] = -b;
            sum[mark] = b;
          } else {
            if (live[b] == 0)
                return false;
            untwisted[nuntwisted++] = sum[mark] = b;
          }
        }
      }

      /* Now we know that every coloring that theta-fits M has its code in
      * "live". We mark the corresponding entry of "live" by theta, that is,
      * set its second, third or fourth bit to 1 */
      if (on != 0) {
        for (i = 0; i < ntwisted; i++)
          live[twisted[i]]   |= 8;
        for (i = 0; i < nuntwisted; i++)
          live[untwisted[i]] |= 4;
      } else {
        for (i = 0; i < ntwisted; i++)
          live[twisted[i]]   |= 2;
        for (i = 0; i < nuntwisted; i++)
          live[untwisted[i]] |= 2;
      }

      return true;
    }
    public static void Checkreality(
      int depth, int[][] weight, int[] live, int[] real, ref int pnreal, int ring, int basecol, int on, ref int pbit, ref int prealterm, int nchar)
    {
      /* For a given matching M, it runs through all signings, and checks which of
      * them have the property that all associated colourings belong to "live". It
      * writes the answers into bits of "real", starting at the point specified by
      * "bit" and "realterm". "basecol" is for convenience in computing the
      * associated colourings; it is zero for matchings not incident with "ring".
      * "on" is nonzero iff the matching is incident with "ring". */

      int i, k, nbits, col, parity;
      int[] choice = new int[8];
      int left;

      nbits = 1 << (depth - 1);
      /* k will run through all subsets of M minus the first match */
      for (k = 0; k < nbits; k++, pbit <<= 1) {
        if (pbit == 0) {
          pbit = 1;
          ++prealterm;

          Debug.Assert((prealterm <= nchar),
            "More than %ld entries in real are needed\n");

        }
        if ((pbit & real[prealterm]) == 0)
          continue;
        col = basecol;
        parity = ring & 1;
        for (i = 1, left = k; i < depth; i++, left >>= 1) {
          if ((left & 1) != 0) {	/* i.e. if a_i=1, where k=a_1+2a_2+4a_3+... */
            parity ^= 1;
            choice[i] = weight[i][1];
            col += weight[i][3];
          } else {
            choice[i] = weight[i][0];
            col += weight[i][2];
          }
        }
        if (parity != 0) {
          choice[depth] = weight[depth][1];
          col += weight[depth][3];
        } else {
          choice[depth] = weight[depth][0];
          col += weight[depth][2];
        }
        if (!Stillreal(col, choice, depth, live, on)) {
          real[prealterm] ^= pbit;
        } else
          pnreal++;
      }
    }

  }
  public class LibReduceContract {
    public static bool Inlive(
      int[] col, int ring, int[] live, int bigno, int[] power)
    {
      /* Same as "record" above, except now it returns whether the colouring is in
      * live, and does not change live. */
      int colno, i, min, max, w;
      int[] weight = new int[5];

      for (i = 1; i < 5; i++)
          weight[i] = 0;
      for (i = 1; i <= ring; i++)
          weight[col[i]] += power[i];
      min = max = weight[4];
      for (i = 1; i <= 2; i++) {
          w = weight[i];
          if (w < min)
      min = w;
          else if (w > max)
      max = w;
      }
      colno = bigno - 2 * min - max;
      if (live[colno] == 0){
        return true;
      } else {
        return false;
      }
    }
    public static void CheckContractSub(
      int[] forbidden, int[] c, int[] contract, int j, int start, int[][] diffangle, int[][] sameangle, int bigno, int ring, int[] live, int[] power)
    {
      int x, u, i;
      int[] dm = new int[5];
      int[] sm = new int[5];

      for (x = 0; x < 1024; x++) {
        while ((forbidden[j] & c[j]) != 0) {
          c[j] <<= 1;
          while ((c[j] & 8) != 0) {
            while (contract[++j] != 0);
            if (j >= start) {
              Console.Write("               ***  Contract confirmed  ***\n\n");
              return;
            }
            c[j] <<= 1;
          }
        }
        if (j == 1) {
          Debug.Assert(Inlive(c, ring, live, bigno, power),
            "       ***  ERROR: INPUT CONTRACT IS INCORRECT  ***\n\n");
          c[j] <<= 1;
          while ((c[j] & 8) != 0) {
            while (contract[++j] != 0);
            if (j >= start) {
              Console.Write("               ***  Contract confirmed  ***\n\n");
              return;
            }
            c[j] <<= 1;
          }
          continue;
        }
        while (contract[--j] != 0);
        dm = diffangle[j];
        sm = sameangle[j];
        c[j] = 1;
        for (u = 0, i = 1; i <= dm[0]; i++)
          u |= c[dm[i]];
        for (i = 1; i <= sm[0]; i++)
          u |= ~c[sm[i]];
        forbidden[j] = u;
      }
      //Debug.Assert(false,
      //  "checkContractSub : It was not good though it was repeated 1024 times!");
    }
  }
}



