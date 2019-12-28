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

      //Debug.Assert((1>2), "hugaguga!");
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
}



