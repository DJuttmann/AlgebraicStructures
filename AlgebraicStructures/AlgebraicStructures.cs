﻿//========================================================================================
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
    void Copy (Monoid rhs);
    void Add (Monoid rhs);
    void SetZero ();
    bool IsZero ();
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
    bool IsOne ();
  }


  public interface Commutative {}


  public interface DivisionRing: Ring
  {
    void Invert ();
    void Divide (DivisionRing rhs);
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

//----------------------------------------------------------------------------------------

  public interface SubGroup <G>: Group where G: Group
  {
    bool FromParent (G g);
    G ToParent ();
  }


  public interface NormalSubGroup <G>: SubGroup <G> where G: Group
  {
  }


  public interface Ideal <R>: Module <R>, NormalSubGroup <R> where R: Commutative, Ring
  {
  }


  public interface PrincipalIdeal <R>: Ideal <R> where R: Commutative, Ring
  {
    bool SetGenerator ();
    bool IsGenerator ();
  }


  public interface SubModule <M, R>: NormalSubGroup <M>, Module <R>
    where M: Module <R>
    where R: Ring
  {
  }


//========================================================================================
// Class Natural
//========================================================================================


  class Natural: Monoid
  {
    public const uint MaxUshort = 1 + (uint) ushort.MaxValue;

    protected List <ushort> Data;


    // Default constructor: Natural set to 0.
    public Natural ()
    {
      Data = new List <ushort> ();
    }

//========================================================================================
// Interface implementations

    public void Copy (Monoid rhs)
    {
      if (rhs is Natural n && n != this)
      {
        Data.Clear ();
        Data.InsertRange (0, n.Data);
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is Natural n)
      {
        int length = Math.Max (Data.Count, n.Data.Count);
        uint sum = 0;
        List <ushort> newData = new List <ushort> ();
        for (int i = 0; i < length; i++)
        {
          sum += (uint) GetData (i) + (uint) n.GetData (i);
          newData.Add ((ushort) (sum % MaxUshort));
          sum /= MaxUshort;
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


    public bool IsZero ()
    {
      return Data.Count == 0;
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
      Copy (this * rhs);
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
        temp /= MaxUshort;
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
          difference.Data [i] = (ushort) ((difference.Data [i] + MaxUshort) - carry);
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
        if (rhsShift <= this)
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


    // Cast from ulong
    public static implicit operator Natural (ulong l)
    {
      return new Natural (l);
    }

//========================================================================================
// Misc.

    // Overloaded constructor: load from Natural.
    public Natural (Natural n)
    {
      Data = new List <ushort> (n.Data);
//      for (int i = 0; i < n.Data.Count; i++)
//        Data.Add (n.Data [i]);
    }

    
    // Overloaded constructor: load from ulong.
    public Natural (ulong l)
    {
      Data = new List <ushort> ();
      while (l > 0)
      {
        Data.Add ((ushort) l);
        l /= MaxUshort;
      }
    }


    public void SetOne ()
    {
      SetZero ();
      Data.Add (1);
    }


    public bool IsOne ()
    {
      return (Data.Count == 1 && Data [0] == 1);
    }


    public static Natural GCD (Natural lhs, Natural rhs)
    {
      Natural a = new Natural (lhs),
              b = new Natural (rhs),
              temp;
      if (a.IsZero ())
        return b;
      while (true)
      {
        temp = a;
        a = b;
        b = temp;
        if (a.IsZero ())
          return b;
        b.DivideWithRemainder (a);
      }
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


    public override string ToString ()
    {
      if (IsZero ())
        return "0";
      StringBuilder str = new StringBuilder ();
      Natural n = new Natural (this),
              b = new Natural (10),
              temp;
      if (n < b)
        return "0123456789" [n.Data [0]].ToString ();
      while (!n.IsZero ())
      {
        temp = n.DivideWithRemainder (b);
        str.Append (n.ToString ());
        n = temp;
      }
      char [] reverse = str.ToString ().ToCharArray ();
      Array.Reverse (reverse);
      return new string (reverse);
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
    protected Natural absValue;
    public Natural AbsValue
    {
      get {return new Natural (absValue);}
      set {absValue.Copy (value);}
    }
    public bool IsNegative;
    

    // Default constructor: Integer set to 0.
    public Integer ()
    {
      absValue = new Natural ();
      IsNegative = false;
    }

//========================================================================================
// Interface implementations

    public void Copy (Monoid rhs)
    {
      if (rhs is Integer i && i != this)
      {
        this.absValue.Copy (i.absValue);
        this.IsNegative = i.IsNegative;
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is Integer n)
      {
        if (IsNegative)
        {
          if (n.IsNegative)
            absValue.Add (n.absValue);
          else
            Copy (n.absValue - absValue);
        }
        else
        {
          if (n.IsNegative)
            Copy (absValue - n.absValue);
          else
            absValue.Add (n.absValue);
        }
      }
    }


    public void SetZero ()
    {
      absValue = new Natural (0);
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
        absValue *= n.absValue;
      }
    }


    public void SetOne ()
    {
      absValue.SetOne ();
      IsNegative = false;
    }


    public bool IsOne ()
    {
      return absValue.IsOne () && !IsNegative;
    }


    public void Scale (Integer scalar)
    {
      IsNegative ^= scalar.IsNegative;
      absValue *= scalar.absValue;
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
    public Integer DivideWithRemainder (Integer rhs)
    {
      Integer quotient = new Integer ();
      quotient.absValue = absValue.DivideWithRemainder (rhs.absValue);
      quotient.IsNegative = IsNegative;
      return quotient.absValue != null ? quotient : null;
    }


    // Division: returns Rational, or null if rhs = 0.
    public static Rational operator / (Integer lhs, Integer rhs)
    {
      if (rhs.IsZero ())
        return null;
      return new Rational (lhs) / new Rational (rhs);
    }


    // <
    public static bool operator < (Integer lhs, Integer rhs)
    {
      if (lhs.Equals (rhs) || (rhs.IsNegative && !lhs.IsNegative))
        return false;
      if (lhs.IsNegative && !rhs.IsNegative)
        return true;
      if (lhs.IsNegative)
        return rhs.absValue < lhs.absValue;
      return lhs.absValue < rhs.absValue;
    }


    // >
    public static bool operator > (Integer lhs, Integer rhs)
    {
      return rhs < lhs;
    }


    // <=
    public static bool operator <= (Integer lhs, Integer rhs)
    {
      return !(rhs < lhs);
    }


    // >=
    public static bool operator >= (Integer lhs, Integer rhs)
    {
      return !(lhs < rhs);
    }


    // Cast from long.
    public static implicit operator Integer (long n)
    {
      return new Integer (n);
    }


    // Cast from Natural.
    public static implicit operator Integer (Natural n)
    {
      return new Integer (n);
    }

//========================================================================================
// Misc

    // Constructor: copy from Integer.
    public Integer (Integer n)
    {
      this.absValue = new Natural (n.absValue);
      this.IsNegative = n.IsNegative;
    }


    // Constructor: copy from Natural.
    public Integer (Natural absValue)
    {
      this.absValue = new Natural (absValue);
      this.IsNegative = false;
    }


    // Constructor: copy from Natural and sign.
    public Integer (Natural absValue, bool negative)
    {
      this.absValue = new Natural (absValue);
      this.IsNegative = negative;
    }


    // Constructor: copy from long.
    public Integer (long n)
    {
      this.IsNegative = n < 0;
      if (this.IsNegative)
        n = -n;
      this.absValue = new Natural ((ulong) n);
    }

    
    // Check if Integer is zero.
    public bool IsZero ()
    {
      return absValue.IsZero ();
    }


    // Override Equals
    public override bool Equals (object obj)
    {
      if (obj is Integer rhs)
      {
        if (IsZero () && rhs.IsZero ())
          return true;
        if (IsNegative == rhs.IsNegative && absValue.Equals (rhs.absValue))
          return true;
      }
      return false;
    }


    // Override ToString
    public override string ToString ()
    {
      if (absValue.IsZero ())
        return "0";
      if (IsNegative)
        return "-" + absValue.ToString ();
      return absValue.ToString ();
    }
  }


//========================================================================================
// Class Rational
//========================================================================================


  class Rational: Field, AlgebraOverField <Rational>, Algebra <Integer>
  {
    private Integer numerator;
    public Integer Numerator
    {
      get {return new Integer (numerator);}
      set
      {
        Numerator = new Integer (value);
        Simplify ();
      }
    }
    private Natural denominator;
    public Natural Denominator
    {
      get {return new Natural (denominator);}
      set
      {
        if (!value.IsZero ())
        {
          denominator = new Natural (value);
          Simplify ();
        }
      }
    }

    
    // Default constructor: Rational set to 0.
    public Rational ()
    {
      numerator = new Integer (0ul);
      denominator = new Natural (1);
    }

//========================================================================================
// Interface implementations

    public void Copy (Monoid rhs)
    {
      if (rhs is Rational r && r != this)
      {
        numerator.Copy (r.numerator);
        denominator.Copy (r.denominator);
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is Rational r)
      {
        Integer rhsNumerator = new Integer (r.numerator);
        numerator.Multiply ((Integer) r.denominator);
        rhsNumerator.Multiply ((Integer) denominator);
        numerator.Add (rhsNumerator);
        denominator.Multiply (r.denominator);
        Simplify ();
      }
    }


    public void SetZero ()
    {
      numerator.SetZero ();
      denominator.SetOne ();
    }


    public bool IsZero ()
    {
      return numerator.IsZero ();
    }


    public void Negative ()
    {
      numerator.Negative ();
    }


    public void Subtract (Group rhs)
    {
      if (rhs is Rational r)
      {
        numerator.Negative ();
        Add (r);
        numerator.Negative ();
      }
    }


    public void SetOne ()
    {
      numerator.SetOne ();
      denominator.SetOne ();
    }


    public bool IsOne ()
    {
      return numerator.IsOne () && denominator.IsOne ();
    }


    public void Multiply (Ring rhs)
    {
      if (rhs is Rational r)
      {
        numerator.Multiply (r.numerator);
        denominator.Multiply (r.denominator);
        Simplify ();
      }
    }


    public void Invert ()
    {
      if (!IsZero ())
      {
        Natural temp = denominator;
        denominator = numerator.AbsValue;
        numerator.AbsValue = temp;
      }
    }


    public void Divide (DivisionRing rhs)
    {
      if (rhs is Rational r && !r.IsZero ())
      {
        Rational d = new Rational (r);
        d.Invert ();
        Multiply (d);
      }
    }


    public void Scale (Rational scalar)
    {
      Multiply (scalar);
    }


    public void Scale (Integer scalar)
    {
      Multiply ((Rational) scalar);
    }

//========================================================================================
// Operators

    // +
    public static Rational operator + (Rational lhs, Rational rhs)
    {
      Rational sum = new Rational (lhs);
      sum.Add (rhs);
      return sum;
    }


    // -
    public static Rational operator - (Rational lhs, Rational rhs)
    {
      Rational difference = new Rational (lhs);
      difference.Subtract (rhs);
      return difference;
    }


    // *
    public static Rational operator * (Rational lhs, Rational rhs)
    {
      Rational product = new Rational (lhs);
      product.Multiply (rhs);
      return product;
    }


    // /
    public static Rational operator / (Rational lhs, Rational rhs)
    {
      Rational quotient = new Rational (lhs);
      quotient.Divide (rhs);
      return quotient;
    }


    // <
    public static bool operator < (Rational lhs, Rational rhs)
    {
      if (lhs.Equals (rhs) || (rhs.numerator.IsNegative && !lhs.numerator.IsNegative))
        return false;
      if (lhs.numerator.IsNegative && !rhs.numerator.IsNegative)
        return true;
      if (lhs.numerator.IsNegative)
        return rhs.numerator.AbsValue * lhs.denominator < 
               lhs.numerator.AbsValue * rhs.denominator;
      return lhs.numerator.AbsValue * rhs.denominator <
             rhs.numerator.AbsValue * lhs.denominator;
    }


    // >
    public static bool operator > (Rational lhs, Rational rhs)
    {
      return rhs < lhs;
    }


    // <=
    public static bool operator <= (Rational lhs, Rational rhs)
    {
      return !(rhs < lhs);
    }


    // >=
    public static bool operator >= (Rational lhs, Rational rhs)
    {
      return !(lhs < rhs);
    }


    // Cast from Natural.
    public static implicit operator Rational (Natural n)
    {
      return new Rational (n);
    }


    // Cast from Integer.
    public static implicit operator Rational (Integer i)
    {
      return new Rational (i);
    }

//========================================================================================
// Misc

    // Constructor: copy from Rational.
    public Rational (Rational r)
    {
      numerator = new Integer (r.numerator);
      denominator = new Natural (r.denominator);
    }


    // Constructor: copy from Integer and Natural.
    public Rational (Integer n, Natural d)
    {
      numerator = new Integer (n);
      if (d.IsZero ())
        denominator = new Natural (1);
      else
        denominator = new Natural (d);
    }

   
    // Constructor: copy from Natural.
    public Rational (Natural n)
    {
      numerator = new Integer (n);
      denominator = new Natural (1);
    }


    // Constructor: copy from Integer.
    public Rational (Integer n)
    {
      numerator = new Integer (n);
      denominator = new Natural (1);
    }


    // Put the fraction in simples form such that GCD (numerator, denominator) = 1.
    private void Simplify ()
    {
      Natural gcd = Natural.GCD (numerator.AbsValue, denominator);
      if (!gcd.IsOne ())
      { // if not coprime, divide out gcd
        numerator = numerator.DivideWithRemainder (gcd);
        denominator /= gcd;
      }
    }


    public override bool Equals (object obj)
    {
      return obj is Rational r && r.numerator == numerator && r.denominator == denominator;
    }


    public override string ToString ()
    {
      return numerator.ToString () +
             (denominator.IsOne () ? "" : "/" + denominator.ToString ());
    }
  }


//========================================================================================
// Class Polynomial <R>
//========================================================================================


  class Polynomial <R>: Algebra <R> where R: Ring, new ()
  {
    protected List <R> Coefficients;
    public R this [int index]
    {
      get
      {
        R Coefficient = new R ();
        if (index < Coefficients.Count)
          Coefficient.Copy (Coefficients [index]);
        return Coefficient;
      }
      set
      {
        for (int i = Coefficients.Count (); i <= index; i++)
          Coefficients.Add (new R ());
        Coefficients [index].Copy (value);
        Normalize ();
      }
    }


    // Default constructor: Polynomial set to 0.
    public Polynomial ()
    {
      Coefficients = new List <R> ();
    }

//========================================================================================
// Interface implementations

    public void Copy (Monoid rhs)
    {
      if (rhs is Polynomial <R> r && r != this)
      {
        Coefficients.Clear ();
        for (int i = 0; i < r.Coefficients.Count; i++)
        {
          Coefficients [i] = new R ();
          Coefficients [i].Copy (r.Coefficients [i]);
        }
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is Polynomial <R> r)
      {
        for (int i = Math.Min (Coefficients.Count, r.Coefficients.Count) - 1; i >= 0; i--)
          Coefficients [i].Add (r.Coefficients [i]);
        for (int i = Coefficients.Count; i < r.Coefficients.Count; i++)
        {
          Coefficients.Add (new R ());
          Coefficients [i].Copy (r.Coefficients [i]);
        }
        Normalize ();
      }
    }


    public void SetZero ()
    {
      Coefficients.Clear ();
    }


    public bool IsZero ()
    {
      return Coefficients.Count == 0;
    }


    public void Negative ()
    {
      for (int i = 0; i < Coefficients.Count; i++)
        Coefficients [i].Negative ();
    }


    public void Subtract (Group rhs)
    {
      if (rhs is Polynomial <R> r)
      {
        Polynomial <R> rhsNegative = new Polynomial <R> (r);
        rhsNegative.Negative ();
        Add (rhsNegative);
      }
    }


    public void Multiply (Ring rhs)
    {
      if (rhs is Polynomial <R> r)
      {
        Copy (this * r);
      }
    }


    public void SetOne ()
    {
      R One = new R ();
      One.SetOne ();
      if (Coefficients.Count == 0)
        Coefficients.Add (One);
      else
      {
        Coefficients.RemoveRange (1, Coefficients.Count - 1);
        Coefficients [0].Copy (One);
      }
    }


    public bool IsOne ()
    {
      return Coefficients.Count == 1 && Coefficients [0].IsOne ();
    }


    public void Scale (R rhs)
    {
      for (int i = 0; i < Coefficients.Count; i++)
        Coefficients [i].Multiply (rhs);
    }

//========================================================================================
// Operators

    // +
    public static Polynomial <R> operator + (Polynomial <R> lhs, Polynomial <R> rhs)
    {
      Polynomial <R> sum = new Polynomial <R> (lhs);
      sum.Add (rhs);
      return sum;
    }


    // -
    public static Polynomial <R> operator - (Polynomial <R> lhs, Polynomial <R> rhs)
    {
      Polynomial <R> difference = new Polynomial <R> (lhs);
      difference.Subtract (rhs);
      return difference;
    }


    // *
    public static Polynomial <R> operator * (Polynomial <R> lhs, Polynomial <R> rhs)
    {
      Polynomial <R> product = new Polynomial <R> ();
      if (lhs.Coefficients.Count != 0 && rhs.Coefficients.Count != 0)
      {
        int size = lhs.Coefficients.Count + rhs.Coefficients.Count - 1;
        int min, max;
        R coefficient, 
          temp = new R ();
        for (int i = 0; i < size; i++)
        {
          coefficient = new R ();
          min = Math.Max (0, i - rhs.Coefficients.Count + 1);
          max = Math.Min (i, lhs.Coefficients.Count - 1);
          for (int j = min; j <= max; j++)
          {
            temp.Copy (lhs.Coefficients [j]);
            temp.Multiply (rhs.Coefficients [i - j]);
            coefficient.Add (temp);
          }
          product.Coefficients.Add (coefficient);
        }
      }
      return product;
    }


    // Cast from R.
    public static implicit operator Polynomial <R> (R r)
    {
      return new Polynomial <R> (r);
    }

//========================================================================================
// Misc.

    // Constructor: Copy from Polynomial <R>.
    public Polynomial (Polynomial <R> p)
    {
      Coefficients = new List <R> ();
      for (int i = 0; i < p.Coefficients.Count; i++)
      {
        Coefficients.Add (new R ());
        Coefficients [i].Copy (p.Coefficients [i]);
      }
    }


    // Constructor: Copy from R.
    public Polynomial (R r)
    {
      Coefficients = new List <R> ();
      Coefficients.Add (new R ());
      Coefficients [0].Copy (r);
    }
    

    // Remove zeros at the end of Coefficients list.
    public void Normalize ()
    {
      int i = Coefficients.Count - 1;
      while (i >= 0 && Coefficients [i].IsZero ())
        i--;
      i++;
      Coefficients.RemoveRange (i, Coefficients.Count - i);
    }


    // Return the degree of the polynomial.
    public int Degree ()
    {
      return Coefficients.Count - 1;
    }


    public override bool Equals (Object obj)
    {
      if (obj is Polynomial <R> p && p.Coefficients.Count == Coefficients.Count)
      {
        for (int i = 0; i < Coefficients.Count; i++)
          if (Coefficients [i].Equals (p.Coefficients [i]))
            return false;
        return true;
      }
      return false;
    }


    public override string ToString ()
    {
      if (Coefficients.Count == 0) // handle zero case
      {
        R zero = new R ();
        zero.SetZero ();
        return zero.ToString ();
      }

      StringBuilder str = new StringBuilder ();
      for (int i = Coefficients.Count - 1; i > 0; i--)
      {
        str.Append (Coefficients [i].ToString ());
        str.Append ("x^");
        str.Append (i.ToString ());
        str.Append (" + ");
      }
      str.Append (Coefficients [0].ToString ());
      return str.ToString ();
    }
  }


//========================================================================================
// Class FieldPolynomial <F>
//========================================================================================


  class FieldPolynomial <F>: Polynomial <F>, Commutative, AlgebraOverField <F>
    where F: Field, new ()
  {

    // Division with remainder; returns quotient, while this is set to remainder.
    // Returns null if rhs = 0;
    public FieldPolynomial <F> DivideWithRemainder (FieldPolynomial <F> rhs)
    {
      FieldPolynomial <F> quotient = new FieldPolynomial <F> ();
      if (rhs.Degree () > Degree ())
        return quotient;
      if (rhs.IsZero ())
        return null;

      int rhsDegree = rhs.Degree ();
      F rhsLeadingCoefficient = rhs.Coefficients [rhsDegree];
      FieldPolynomial <F> xPower = new FieldPolynomial <F> ();
      F scale = new F ();
      F zero = new F ();
      zero.SetZero ();

      for (int power = Degree () - rhsDegree; power >= 0; power--)
      {
        xPower.SetZero ();
        scale.Copy (this [power + rhsDegree]);
        scale.Divide (rhsLeadingCoefficient);
        xPower [power] = scale;
        xPower.Multiply (rhs);
        Subtract (xPower);
        quotient.Add (xPower);
        this [power + rhsDegree] = zero;
      }
      return quotient;
    }


    // /
    public static FieldPolynomial <F> operator / (FieldPolynomial <F> lhs, FieldPolynomial <F> rhs)
    {
      FieldPolynomial <F> remainder = new FieldPolynomial <F> ();
      remainder.Copy (lhs);
      return remainder.DivideWithRemainder (rhs);
    }


    // %
    public static FieldPolynomial <F> operator % (FieldPolynomial <F> lhs, FieldPolynomial <F> rhs)
    {
      FieldPolynomial <F> remainder = new FieldPolynomial <F> ();
      remainder.Copy (lhs);
      remainder.DivideWithRemainder (rhs);
      return remainder;
    }
  }


//========================================================================================
// class CyclicGroup <Nat>
//========================================================================================


  class CyclicGroup <Nat>: Abelian, Group where Nat: _, new ()
  {
    protected Natural modulo;
    public Natural Modulo
    {
      get {return new Natural (modulo);}
      set {modulo.Copy (value);}
    }
    protected Natural number;
    public Natural Number
    {
      get {return new Natural (number);}
      set {number.Copy (value);}
    }
    // {get; private set;}


    public CyclicGroup ()
    {
      Nat n = new Nat ();
      modulo = new Natural ((ulong) n.ToInt ());
      number = new Natural ();
    }

//========================================================================================
// Interface implementations

    public void Copy (Monoid rhs)
    {
      if (rhs is CyclicGroup <Nat> n && n != this)
      {
        modulo = n.modulo;
        number = n.number;
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is CyclicGroup <Nat> n)
      {
        number.Add (n.number);
        number.DivideWithRemainder (modulo);
      }
    }


    public void SetZero ()
    {
      number.SetZero ();
    }


    public bool IsZero ()
    {
      return number.IsZero ();
    }


    public void Negative ()
    {
      number.Copy ((modulo - number).AbsValue);
    }


    public void Subtract (Group rhs)
    {
      if (rhs is CyclicGroup <Nat> n)
      {
        if (n.number > number)
        {
          number.Add (modulo);
          number.Difference (n.number);
        }
        else
          number.Difference (n.number);
      }
    }

//========================================================================================
// Operators.

    public static CyclicGroup <Nat> operator + (CyclicGroup <Nat> lhs,
                                                CyclicGroup <Nat> rhs)
    {
      CyclicGroup <Nat> sum = new CyclicGroup <Nat> (lhs);
      sum.Add (rhs);
      return sum;
    }


    public static CyclicGroup <Nat> operator - (CyclicGroup <Nat> lhs,
                                                CyclicGroup <Nat> rhs)
    {
      CyclicGroup <Nat> difference = new CyclicGroup <Nat> (lhs);
      difference.Subtract (rhs);
      return difference;
    }

// [wip] add these


//========================================================================================
// Misc.

    public CyclicGroup (Natural number)
    {
      Nat n = new Nat ();
      modulo = new Natural ((ulong) n.ToInt ());
      this.number = new Natural (number);
      this.number.DivideWithRemainder (modulo);
    }


    public CyclicGroup (CyclicGroup <Nat> c)
    {
      modulo = new Natural (c.modulo);
      number = new Natural (c.number);
    }


    public override string ToString ()
    {
      return number.ToString ();
    }
  }


//========================================================================================
// Direct Product Classes
//========================================================================================
// class DirectProductGroup <G, H>

 
  class DirectProductGroup <G, H>: Group
    where G: Group, new ()
    where H: Group, new ()
  {
    protected G item1;
    public G Item1
    {
      get 
      {
        G g = new G ();
        g.Copy (item1);
        return g;
      }
      set {item1.Copy (value);}
    }
    protected H item2;
    public G Item2
    {
      get 
      {
        G g = new G ();
        g.Copy (item2);
        return g;
      }
      set {item2.Copy (value);}
    }


    // Default constructor: set to zero.
    public DirectProductGroup ()
    {
      item1 = new G ();
      item2 = new H ();
    }

//----------------------------------------------------------------------------------------
// Interface implementations.

    public void Copy (Monoid rhs)
    {
      if (rhs is DirectProductGroup <G, H> p && p != this)
      {
        item1.Copy (p.item1);
        item2.Copy (p.item2);
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is DirectProductGroup <G, H> p)
      {
        item1.Add (p.item1);
        item2.Add (p.item2);
      }
    }


    public void SetZero ()
    {
      item1.SetZero ();
      item2.SetZero ();
    }


    public bool IsZero ()
    {
      return item1.IsZero () && item2.IsZero ();
    }


    public void Negative ()
    {
      item1.Negative ();
      item2.Negative ();
    }


    public void Subtract (Group rhs)
    {
      if (rhs is DirectProductGroup <G, H> p)
      {
        item1.Subtract (p.item1);
        item2.Subtract (p.item2);
      }
    }

//----------------------------------------------------------------------------------------
// Operators.

    public static DirectProductGroup <G, H> operator + (DirectProductGroup <G, H> lhs,
                                                  DirectProductGroup <G, H> rhs)
    {
      DirectProductGroup <G, H> sum = new DirectProductGroup <G, H> (lhs);
      sum.Add (rhs);
      return sum;
    }


    public static DirectProductGroup <G, H> operator - (DirectProductGroup <G, H> lhs,
                                                  DirectProductGroup <G, H> rhs)
    {
      DirectProductGroup <G, H> difference = new DirectProductGroup <G, H> (lhs);
      difference.Subtract (rhs);
      return difference;
    }

//----------------------------------------------------------------------------------------
// Misc.

    // Constructor: Copy from ProductGroup <G, H>.
    public DirectProductGroup (DirectProductGroup <G, H> p)
    {
      item1 = new G ();
      item2 = new H ();
      item1.Copy (p.item1);
      item2.Copy (p.item2);
    }


    // Constructor: Copy from groups G, H.
    public DirectProductGroup (G g, H h)
    {
      item1 = new G ();
      item2 = new H ();
      item1.Copy (g);
      item2.Copy (h);
    }


    public override bool Equals (object obj)
    {
      if (obj is DirectProductGroup <G, H> p)
        return item1.Equals (p.item1) && item2.Equals (p.item2);
      return false;
    }


    public override string ToString ()
    {
      return "(" + item1.ToString () + ", " + item2.ToString () + ")";
    }
  }


//========================================================================================
// class DirectProductModule <M, N, R>


  class DirectProductModule <M, N, R>: DirectProductGroup <M, N>, Module <R>
    where M: Module <R>, new ()
    where N: Module <R>, new ()
    where R: Ring, new ()
  {
    public void Scale (R rhs)
    {
      item1.Scale (rhs);
      item2.Scale (rhs);
    }
  }


//========================================================================================
// class DirectProductRing <R, S>

  class DirectProductRing <R, S>: DirectProductGroup <R, S>, Ring
    where R: Ring, new ()
    where S: Ring, new ()
  {
    public void Multiply (Ring rhs)
    {
      if (rhs is DirectProductRing <R, S> p)
      {
        item1.Multiply (p.item1);
        item2.Multiply (p.item2);
      }
    }


    public void SetOne ()
    {
      item1.SetOne ();
      item2.SetOne ();
    }


    public bool IsOne ()
    {
      return item1.IsOne () && item2.IsOne ();
    }
  }


//========================================================================================
// class DirectProductAlgebra <A, B, R>


  class DirectProductAlgebra <A, B, R>: DirectProductRing <A, B>, Algebra <R>
    where A: Algebra <R>, new ()
    where B: Algebra <R>, new ()
    where R: Ring, new ()
  {
    public void Scale (R rhs)
    {
      item1.Scale (rhs);
      item2.Scale (rhs);
    }
  }


//========================================================================================
// class DirectProductVectorSpace <V, W, F>


  class DirectProductVectorSpace <V, W, F>: DirectProductModule <V, W, F>, VectorSpace <F>
    where V: VectorSpace <F>, new ()
    where W: VectorSpace <F>, new ()
    where F: Field, new ()
  {
  }


//========================================================================================
// class DirectProductAlgebraOverField <V, W, F>


  class DirectProductAlgebraOverField <A, B, F>: DirectProductAlgebra <A, B, F>, Algebra <F>
    where A: Algebra <F>, new ()
    where B: Algebra <F>, new ()
    where F: Field, new ()
  {
  }


//========================================================================================
// Quotient Classes
//========================================================================================
// class QuotientGroup <G, H>


  class QuotientGroup <G, H>: Group
    where G: Group, new ()
    where H: NormalSubGroup <G>, new ()
  {
    protected G Representative;


    public QuotientGroup ()
    {
      Representative = new G ();
    }

//----------------------------------------------------------------------------------------
// Interface implementations.

    public void Copy (Monoid rhs)
    {
      if (rhs is QuotientGroup <G, H> q && q != this)
        Representative.Copy (q.Representative);
    }


    public void Add (Monoid rhs)
    {
      if (rhs is QuotientGroup <G, H> q)
        Representative.Add (q.Representative);
    }


    public void SetZero ()
    {
      Representative.SetZero ();
    }


    public bool IsZero ()
    {
      QuotientGroup <G, H> zero = new QuotientGroup <G, H> ();
      return Equals (zero);
    }


    public void Negative ()
    {
      Representative.Negative ();
    }


    public void Subtract (Group rhs)
    {
      if (rhs is QuotientGroup <G, H> q)
        Representative.Subtract (q.Representative);
    }

//----------------------------------------------------------------------------------------
// Operators.

    public static QuotientGroup <G, H> operator + (QuotientGroup <G, H> lhs,
                                                   QuotientGroup <G, H> rhs)
    {
      QuotientGroup <G, H> sum = new QuotientGroup <G, H> (lhs);
      sum.Add (rhs);
      return sum;
    }


    public static QuotientGroup <G, H> operator - (QuotientGroup <G, H> lhs,
                                                   QuotientGroup <G, H> rhs)
    {
      QuotientGroup <G, H> difference = new QuotientGroup <G, H> (lhs);
      difference.Subtract (rhs);
      return difference;
    }


    public static implicit operator QuotientGroup <G, H> (G g)
    {
      return new QuotientGroup <G, H> (g);
    }

//----------------------------------------------------------------------------------------
// Misc.

    public QuotientGroup (QuotientGroup <G, H> rhs)
    {
      Representative = new G ();
      Representative.Copy (rhs.Representative);
    }


    public QuotientGroup (G rhs)
    {
      Representative = new G ();
      Representative.Copy (rhs);
    }


    public override bool Equals (Object obj)
    {
      if (obj is QuotientGroup <G, H> q)
      {
        G difference = new G ();
        H test = new H ();
        difference.Copy (Representative);
        difference.Subtract (q.Representative);
        if (test.FromParent (difference))
          return true;
      }
      return false;
    }


    public override string ToString ()
    {
      return "[" + Representative.ToString () + "]"; 
    }
  }


//========================================================================================
// class QuotientRing <R, S>


  class QuotientRing <R, I>: QuotientGroup <R, I>, Commutative, Ring
    where R: Commutative, Ring, new ()
    where I: Ideal <R>, new ()
  {

    public QuotientRing ()
    {
      Representative = new R ();
    }

//----------------------------------------------------------------------------------------

    public void Multiply (Ring rhs)
    {
      if (rhs is QuotientRing <R, I> q)
      {
        Representative.Multiply (q.Representative);
      }
    }


    public void SetOne ()
    {
      Representative.SetOne ();
    }


    public bool IsOne ()
    {
      QuotientRing <R, I> one = new QuotientRing <R, I> ();
      one.SetOne ();
      return Equals (one);
    }

//----------------------------------------------------------------------------------------
// Misc.

    public QuotientRing (QuotientRing <R, I> rhs)
    {
      Representative = new R ();
      Representative.Copy (rhs.Representative);
    }


    public QuotientRing (R rhs)
    {
      Representative = new R ();
      Representative.Copy (rhs);
    }
  }

//========================================================================================
// class QuotientModule <M, N>


  class QuotientModule <M, N, R>: QuotientGroup <M, N>, Module <R>
    where M: Module <R>, new ()
    where N: SubModule <M, R>, new ()
    where R: Commutative, Ring, new ()
  {

    public QuotientModule ()
    {
      Representative = new M ();
    }

//----------------------------------------------------------------------------------------

    public void Scale (R scalar)
    {
      Representative.Scale (scalar);
    }

//----------------------------------------------------------------------------------------
// Misc.

    public QuotientModule (QuotientModule <M, N, R> rhs)
    {
      Representative = new M ();
      Representative.Copy (rhs.Representative);
    }


    public QuotientModule (M rhs)
    {
      Representative = new M ();
      Representative.Copy (rhs);
    }
  }


//========================================================================================
// class IdealXSquaredPlus1 <P, R>
//========================================================================================


  class IdealXSquaredPlus1 <P, F>: Ideal <P>
    where P: FieldPolynomial <F>, new ()
    where F: Field, new ()
  {
    protected P polynomial;
    public P Polynomial
    {
      get 
      {
        P p = new P ();
        p.Copy (polynomial);
        return p;
      }
      set
      {
        polynomial.Copy (value);
      }
    }
    static private readonly P Generator;


    // Set the Ideal's Generator.
    static IdealXSquaredPlus1 ()
    {
      F one = new F ();
      one.SetOne ();
      Generator = new P ();
      Generator [0] = one;
      Generator [1] = one;
    }

    
    // Default constructor.
    public IdealXSquaredPlus1 ()
    {
      polynomial = new P ();
    }

//========================================================================================
// Interface implementations.

    public void Copy (Monoid rhs)
    {
      if (rhs is IdealXSquaredPlus1 <P, F> i && i != this)
      {
        polynomial = new P ();
        polynomial.Copy (i.polynomial);
      }
    }


    public void Add (Monoid rhs)
    {
      if (rhs is IdealXSquaredPlus1 <P, F> i)
      {
        polynomial.Add (i.polynomial);
      }
    }


    public void SetZero ()
    {
      polynomial.SetZero ();
    }


    public bool IsZero ()
    {
      return polynomial.IsZero ();
    }


    public void Negative ()
    {
      polynomial.Negative ();
    }


    public void Subtract (Group rhs)
    {
      if (rhs is IdealXSquaredPlus1 <P, F> i)
      {
        polynomial.Subtract (i.polynomial);
      }
    }


    public void Scale (P scalar)
    {
      polynomial.Multiply (scalar);
    }


    public bool FromParent (P rhs)
    {
      P rhsCopy = new P ();
      rhsCopy.Copy (rhs);
      rhsCopy.DivideWithRemainder (Generator);
      if (rhsCopy.IsZero ())
      {
        polynomial.Copy (rhs);
        return true;
      }
      return false;
    }


    public P ToParent ()
    {
      P p = new P ();
      p.Copy (polynomial);
      return p;
    }
  }


//========================================================================================
// Natural Numbers as Types
//========================================================================================


  class _
  {
    public override string ToString () {return "";}
    public _ () {}
    public int ToInt ()
    {
      string s = ToString ();
      return s.Length == 0 ? 0 : Int32.Parse (s);
    }
  }

  class _0 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "0" + new T ().ToString ();}
  }

  class _1 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "1" + new T ().ToString ();}
  }

  class _2 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "2" + new T ().ToString ();}
  }

  class _3 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "3" + new T ().ToString ();}
  }

  class _4 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "4" + new T ().ToString ();}
  }

  class _5 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "5" + new T ().ToString ();}
  }

  class _6 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "6" + new T ().ToString ();}
  }

  class _7 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "7" + new T ().ToString ();}
  }

  class _8 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "8" + new T ().ToString ();}
  }

  class _9 <T>: _ where T: _, new ()
  {
    public override string ToString () {return "9" + new T ().ToString ();}
  }


//========================================================================================
// End
//========================================================================================

}



namespace Program 
{
  using AlgebraicStructures;
  class Program
  {
    static void Main (string [] args)
    {
      /*
      Polynomial <Rational> m = new Polynomial <Rational> ();
      Polynomial <Rational> n = new Polynomial <Rational> ();

      m [0] = new Rational (1, 2);
      m [1] = new Rational (2, 3);

      n [0] = new Rational (3, 4);
      n [1] = new Rational (4, 1);


      Natural a = new Natural (156254468629);
      Natural b = new Natural (4321);
      Console.WriteLine (a);
      Console.WriteLine (b);

      Console.WriteLine (m);
      Console.WriteLine (n);
      Console.WriteLine (m + n);
      Console.WriteLine (m * n);

      CyclicGroup <_5 <_9 <_7 <_>>>> c = new CyclicGroup <_5 <_9 <_7 <_>>>> (1597);
      Console.WriteLine ("test " + c.ToString ());
      Console.WriteLine (1597 % 597);

      DirectProductModule <Rational, Rational, Integer> s = 
        new DirectProductModule <Rational, Rational, Integer> ();
      s.Item1 = new Rational (1, 2);
      s.Item2 = new Rational (3, 5);
      Integer t = new Integer (6ul);
      Console.WriteLine (s);
      Console.WriteLine (t);
      s.Scale (t);
      Console.WriteLine (s);
      */

      Natural n = new Natural (123);
      n.Copy (n);
      n.Add (n);
      Console.WriteLine (n);



      Console.ReadKey ();
    }
  }
}
