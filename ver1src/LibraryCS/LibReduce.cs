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
      int d;

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
          Debug.Assert((contract[a]==0 || contract[b]==0),
            "         ***  ERROR: CONTRACT IS NOT SPARSE  ***\n\n");

          if (a > c) {
            d = (angle[c][0] >= 4) ? 4 : ++angle[c][0];
            angle[c][d] = a;
            if ((contract[a] != 0) && (contract[b] != 0) && (contract[c] != 0))
                diffangle[c][++diffangle[c][0]] = a;
            if (contract[b] != 0)
                sameangle[c][++sameangle[c][0]] = a;
          }
          if (b > c) {
            d = (angle[c][0] >= 4) ? 4 : ++angle[c][0];
            angle[c][d] = b;
            if ((contract[a] != 0) && (contract[b] != 0) && (contract[c] != 0))
                diffangle[c][++diffangle[c][0]] = b;
            if (contract[a] != 0)
                sameangle[c][++sameangle[c][0]] = b;
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
      Console.Write("\n              {0}\n", totalcols - extent);
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
}



