using System;
using System.Diagnostics;

namespace LibraryCS {
  public static class LibReduceStrip {
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
          inter = Ininterval(graph[v + 2], done);
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
          d = graph[max[h] + 2][0+1];
          if (d > maxdeg) {
              maxdeg = d;
              best = max[h];
          }
        }
        /* So now, the vertex "best" will be the next vertex to be done */

        d = graph[best + 2][0 + 1];
        first = 1;
        previous = done[graph[best + 2][d + 1]];

        while ((previous) || (!done[graph[best + 2][first + 1]])) {
          previous = done[graph[best + 2][1 + first++]];
          if (first > d) {
            first = 1;
            break;
          }
        }

        for (h = first; done[graph[best + 2][h + 1]]; h++) {
          edgeno[best][graph[best + 2][h + 1]] = term;
          edgeno[graph[best + 2][h + 1]][best] = term;
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
  public static class LibReduceUpdate {
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
      int[] untwisted = new int[64];

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
      int depth, int[][] weight, int[] live, sbyte[] real, ref int pnreal, int ring, int basecol, int on, ref sbyte pbit, ref int prealterm, int nchar)
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
  public static class LibReduceContract {
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
      if (live[colno] == 0) {
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

      for (x = 0; x < 2097152; x++) {
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

        if (j <= 0) return;

        while (contract[--j] != 0);

        dm = diffangle[j];
        sm = sameangle[j];
        c[j] = 1;
        for (u = 0, i = 1; i <= dm[0]; i++) {
          if (i >= 5) break;
          u |= c[dm[i]];
        }
        for (i = 1; i <= sm[0]; i++) {
          if (i >= 5) break;
          u |= ~c[sm[i]];
        }
        forbidden[j] = u;
      }
      Debug.Assert(false,
        "checkContractSub : It was not good though it was repeated 2097152 times!");
    }
  }
}



