//========================================================================================
// AlgebraicStructures by Daan Juttmann
// Created: 2017-11-24
// License: GNU General Public License 3.0 (https://www.gnu.org/licenses/gpl-3.0.en.html).
//========================================================================================

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace AlgebraicStructures
{

//========================================================================================
// Interfaces
//========================================================================================


  public interface Monoid
  {
    void Add (Monoid rhs);
    void SetZero ();
  }


  public interface Group: Monoid
  {
    void Negative ();
    void Subtract (Group rhs);
  }


  public interface Abelian {}


  public interface Ring: Abelian, Group
  {
    void Multiply (Ring rhs);
    void SetOne ();
  }


  public interface Commutative {}


  public interface DivisionRing: Ring
  {
    void Invert ();
    void Divide ();
  }


  public interface Field: Commutative, DivisionRing
  {
  }


  public interface Module <R>: Abelian, Group where R: Ring
  {
    void Scale (R scalar);
  }


  public interface VectorSpace <F>: Module <F> where F: Field
  {
  }


  public interface Algebra <R>: Ring, Module <R> where R: Ring
  {
  }


  public interface AlgebraOverField <F>: VectorSpace <F>, Algebra <F> where F: Field
  {
  }


//========================================================================================
// Class Constants
//========================================================================================


  class Constants
  {
    public const uint MaxUshort = 1 + (uint) ushort.MaxValue;
  }


//========================================================================================
// Class Natural
//========================================================================================


  class Natural: Monoid
  {
    private List <ushort> Data;


    // Default constructor: Natural set to 0.
    public Natural ()
    {
      Data = new List <ushort> ();
    }

//========================================================================================
// Interface implementations

    public void Add (Monoid obj)
    {
      if (obj is Natural rhs)
      {
        int length = Math.Max (Data.Count, ((Natural) rhs).Data.Count);
        uint sum = 0;
        List <ushort> newData = new List <ushort> ();
        for (int i = 0; i < length; i++)
        {
          sum += (uint) GetData (i) + (uint) ((Natural) rhs).GetData (i);
          newData.Add ((ushort) (sum % Constants.MaxUshort));
          sum /= Constants.MaxUshort;
        }
        if (sum > 0)
          newData.Add ((ushort) (sum));
        Data = newData;
      }
    }


    public void SetZero ()
    {
      Data.RemoveRange (0, Data.Count);
    }

//========================================================================================
// Operators

    // +
    public static Natural operator + (Natural lhs, Natural rhs)
    {
      Natural sum = new Natural (lhs);
      sum.Add (rhs);
      return sum;
    }


    // Multiplication
    public void Multiply (Natural rhs)
    {
      Data = (this * rhs).Data;
    }


    // *
    public static Natural operator * (Natural lhs, Natural rhs)
    {
      Natural product = new Natural ();
      ulong temp = 0;
      int size = lhs.Data.Count + rhs.Data.Count;
      int min, max;
      for (int i = 0; i < size; i++)
      {
        min = Math.Max (0, i - rhs.Data.Count + 1);
        max = Math.Min (i, lhs.Data.Count - 1);
        for (int j = min; j <= max; j++)
        {
          temp += (ulong) lhs.Data [j] * (ulong) rhs.Data [i - j];
        }
        product.Data.Add ((ushort) temp);
        temp /= Constants.MaxUshort;
      }
      if (product.Data [size - 1] == 0)
        product.Data.RemoveAt (size - 1);
      return product;
    }


    // Difference (absolute)
    public void Difference (Natural rhs)
    {
      Data = (this - rhs).AbsValue.Data;
    }


    // -
    public static Integer operator - (Natural lhs, Natural rhs)
    {
      if (lhs < rhs)
      {
        Integer diff = (rhs - lhs);
        diff.Negative ();
        return diff;
      }
      Natural difference = new Natural (lhs);
      uint carry = 0;
      for (int i = 0; i < difference.Data.Count; i++)
      {
        carry += (uint) rhs.GetData (i);
        if ((uint) difference.Data [i] >= carry)
        {
          difference.Data [i] -= (ushort) carry;
          carry = 0;
        }
        else
        {
          difference.Data [i] = (ushort) ((difference.Data [i] + Constants.MaxUshort) - carry);
          carry = 1;
        }
      }
      difference.Normalize ();
      return new Integer (difference, false);
    }


    // Bitshift left
    public void ShiftLeft (uint power)
    {
      int bigShift = (int) (power / 16u);
      ushort smallShift = (ushort) (power % 16u);
      ushort smallShiftNegative = (ushort) (16 - smallShift);
      ushort carry = 0;
      ushort data;

      // Small Shift.
      for (int i = 0; i < Data.Count; i++)
      {
        data = Data [i];
        Data [i] = (ushort) ((data << smallShift) | carry);
        carry = (ushort) (data >> smallShiftNegative);
      }
      if (carry > 0)
        Data.Add (carry);

      // Big shift.
      if (bigShift > 0)
      {
        for (uint i = 0; i < bigShift; i++)
          Data.Add (0);
        for (int i = Data.Count - 1; i >= bigShift; i--)
        {
          Data [i] = Data [i - bigShift];
        }
        for (int i = 0; i < bigShift; i++)
          Data [i] = 0;
      }
    }
    

    // Bitshift right
    public void ShiftRight (uint power)
    {
      int bigShift = (int) (power / 16u);
      ushort smallShift = (ushort) (power % 16u);
      ushort smallShiftNegative = (ushort) (16 - smallShift);
      ushort carry = 0;
      ushort data;

      // Big shift
      if (bigShift > 0)
      {
        int i = 0;
        for (; i < Data.Count - bigShift; i++)
          Data [i] = Data [i + bigShift];
        Data.RemoveRange (i, bigShift);
      }

      // Small Shift.
      for (int i = Data.Count - 1; i >= 0; i--)
      {
        data = Data [i];
        Data [i] = (ushort) ((data >> smallShift) | carry);
        carry = (ushort) (data << smallShiftNegative);
      }
      Normalize ();
    }


    // Division with remainder; returns quotient, while this is set to remainder.
    // Returns null if rhs = 0;
    public Natural DivideWithRemainder (Natural rhs)
    {
      Natural quotient = new Natural (0);
      if (rhs > this)
        return quotient;
      if (rhs.IsZero ())
        return null;

      uint maxShift = (uint) ((Data.Count - rhs.Data.Count + 1) * 16);
      Natural rhsShift = new Natural (rhs);
      Natural bit = new Natural (1);
      rhsShift.ShiftLeft (maxShift);
      bit.ShiftLeft (maxShift);

      for (int i = 0; i <= maxShift; i++)
      {
        if (rhsShift < this)
        {
          this.Difference (rhsShift);
          quotient.Add (bit);
        }
        rhsShift.ShiftRight (1);
        bit.ShiftRight (1);
      }
      return quotient;
    }


    // /
    public static Natural operator / (Natural lhs, Natural rhs)
    {
      Natural temp = new Natural (lhs);
      return temp.DivideWithRemainder (rhs);
    }


    // %
    public static Natural operator % (Natural lhs, Natural rhs)
    {
      Natural temp = new Natural (lhs);
      temp.DivideWithRemainder (rhs);
      return temp;
    }

    
    // <
    public static bool operator < (Natural lhs, Natural rhs)
    {
      if (lhs.Data.Count < rhs.Data.Count)
        return true;
      if (lhs.Data.Count > rhs.Data.Count)
        return false;
      for (int i = lhs.Data.Count - 1; i >=0; i--)
      {
        if (lhs.Data [i] < rhs.Data [i])
          return true;
        if (lhs.Data [i] > rhs.Data [i])
          return false;
      }
      return false;
    }


    // >
    public static bool operator > (Natural lhs, Natural rhs)
    {
      return rhs < lhs;
    }


    // <=
    public static bool operator <= (Natural lhs, Natural rhs)
    {
      return !(rhs < lhs);
    }


    // >=
    public static bool operator >= (Natural lhs, Natural rhs)
    {
      return !(lhs < rhs);
    }

//========================================================================================
// Misc.

    // Overloaded constructor: load from Natural.
    public Natural (Natural n)
    {
      Data = new List <ushort> ();
      for (int i = 0; i < n.Data.Count; i++)
        Data.Add (n.Data [i]);
    }

    
    // Overloaded constructor: load from ulong.
    public Natural (ulong l)
    {
      Data = new List <ushort> ();
      while (l > 0)
      {
        Data.Add ((ushort) l);
        l /= Constants.MaxUshort;
      }
    }


    // Check if Integer is zero.
    public bool IsZero ()
    {
      return Data.Count == 0;
    }


    // Override Equals.
    public override bool Equals (object obj)
    {
      if (obj is Natural rhs)
      {
        if (Data.Count != rhs.Data.Count)
          return false;
        for (int i = 0; i < Data.Count; i++)
          if (Data [i] != rhs.Data [i])
            return false;
        return true;
      }
      return false;
    }


    // Override ToString.
    public override string ToString ()
    {
      if (Data.Count == 0)
        return "0";
      char [] DigitsBinary = new [] {'0', '1'};
      StringBuilder str = new StringBuilder ();
      StringBuilder block = new StringBuilder ();
      int i = Data.Count - 1;

      // Write first block.
      ushort value = Data [i];
      while (value > 0)
      {
        block.Append (DigitsBinary [value % 2]);
        value /= 2;
      }
      for (int j = block.Length - 1; j >= 0; j--)
        str.Append (block [j]);
      i--;

      // Write other blocks.
      for (; i >= 0; i--)
      {
        block.Clear ();
        str.Append ("'");
        value = Data [i];
        for (int j = 0; j < 16; j++)
        {
          block.Append (DigitsBinary [value % 2]);
          value /= 2;
        }
        for (int j = block.Length - 1; j >= 0; j--)
          str.Append (block [j]);
      }

      return str.ToString ();
    }


    // Safely get values from the Data list; returns 0 if index >= Data.Count.
    private ushort GetData (int index)
    {
      if (index < Data.Count)
        return Data [index];
      return 0;
    }


    // Rremove zeros at end of Data list.
    private void Normalize ()
    {
      int i = Data.Count - 1;
      while (i >= 0 && Data [i] == 0)
        i--;
      i++;
      Data.RemoveRange (i, Data.Count - i);
    }
  }


//========================================================================================
// Class Integer
//========================================================================================


  class Integer: Commutative, Algebra <Integer>
  {
    public Natural AbsValue;
    public bool IsNegative;
    

    // Default constructor: Integer set to 0.
    public Integer ()
    {
      AbsValue = new Natural ();
      IsNegative = false;
    }

//========================================================================================
// Interface implementations

    public void Add (Monoid rhs)
    {
      // [wip] Implement this!
    }


    public void SetZero ()
    {
      AbsValue = new Natural (0);
    }


    public void Negative ()
    {
      IsNegative = !IsNegative;
    }


    // Subtract
    public void Subtract (Group rhs)
    {
      if (rhs is Integer n)
      {
        Integer rhsNegative = new Integer (n);
        rhsNegative.Negative ();
        Add (rhsNegative);
      }
    }


    public void Multiply (Ring rhs)
    {
      if (rhs is Integer n)
      {
        IsNegative ^= n.IsNegative;
        AbsValue *= n.AbsValue;
      }
    }


    public void SetOne ()
    {
      AbsValue = new Natural (1);
      IsNegative = false;
    }


    public void Scale (Integer scalar)
    {
      IsNegative ^= scalar.IsNegative;
      AbsValue *= scalar.AbsValue;
    }

//========================================================================================
// Operators

    // +
    public static Integer operator + (Integer lhs, Integer rhs)
    {
      Integer sum = new Integer (lhs);
      sum.Add (rhs);
      return (sum);
    }


    // -
    public static Integer operator - (Integer lhs, Integer rhs)
    {
      Integer difference = new Integer (lhs);
      difference.Subtract (rhs);
      return (difference);
    }

    
    // *
    public static Integer operator * (Integer lhs, Integer rhs)
    {
      Integer product = new Integer (lhs);
      product.Multiply (rhs);
      return (product);
    }


    // Division with remainder; returns quotient, while this is set to remainder.
    // Returns null if rhs = 0;
    public Integer Division (Integer rhs)
    {
      Integer quotient = new Integer ();
      quotient.AbsValue = AbsValue.DivideWithRemainder (rhs.AbsValue);
      quotient.IsNegative = IsNegative;
      return quotient.AbsValue != null ? quotient : null;
    }

//========================================================================================
// Misc

    // Constructor: copy from Integer.
    public Integer (Integer n)
    {
      this.AbsValue = n.AbsValue;
      this.IsNegative = n.IsNegative;
    }


    // Constructor: copy from Natural and sign.
    public Integer (Natural absValue, bool negative)
    {
      this.AbsValue = absValue;
      this.IsNegative = negative;
    }


    // Check if Integer is zero.
    public bool IsZero ()
    {
      return AbsValue.IsZero ();
    }


    // Override Equals
    public override bool Equals (object obj)
    {
      if (obj is Integer rhs)
      {
        if (IsZero () && rhs.IsZero ())
          return true;
        if (IsNegative == rhs.IsNegative && AbsValue.Equals (rhs.AbsValue))
          return true;
      }
      return false;
    }


    // Override ToString
    public override string ToString ()
    {
      if (AbsValue.IsZero ())
        return "0";
      if (IsNegative)
        return "-" + AbsValue.ToString ();
      return AbsValue.ToString ();
    }
  }
}



namespace Program 
{
  using AlgebraicStructures;
  class Program
  {
    static void Main (string [] args)
    {
      Natural m = new Natural (987654321ul);
      Natural n = new Natural (123456789ul);
      Console.WriteLine (m.ToString ());
      Console.WriteLine (n.ToString ());

      Natural temp = new Natural (m);
      temp.Difference (n);

      Console.WriteLine (m + n);
      Console.WriteLine (m - n);

      Console.WriteLine (m.DivideWithRemainder (n).ToString ());
      Console.WriteLine (m.ToString ());

      Console.ReadKey ();
    }
  }
}
