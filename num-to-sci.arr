import lists as L

#################################################
# Numerical functions

# round digits to something reasonable
fun round-digits(val, digits):
  num-round(val * num-expt(10, digits)) / num-expt(10, digits)
where:
  round-digits(1.24, 1) is 1.2
  round-digits(num-sqrt(2), 3) is 1.414
end

# allow custom log bases
fun log-base(base, val):
  lg = num-log(val) / num-log(base)
  lg-round = round-digits(lg, 4)
  if roughly-equal(lg-round, lg) and roughly-equal(num-expt(base, lg-round), val):
    lg-round
  else:
    lg
  end
where:
  log-base(3, 9) is 2
  log-base(3, 1/9) is -2
  num-log(9) / num-log(3) satisfies num-is-roughnum
  log-base(4, 32) is 2.5
end

# shortcut alias for log and ln
fun log(n): log-base(10, n) end
ln = num-log

# utility functions
fun fake-num-to-fixnum(n) block:
  var s = num-to-string(num-to-roughnum(n))
  var len = string-length(s)
  s := string-substring(s, 1, len)
  len := len - 1
  expt-position = string-index-of(s, 'e')
  if expt-position == -1: s
  else:
    if string-substring(s, expt-position + 1, expt-position + 2) == '+':
      string-substring(s, 0, expt-position) + string-substring(s, expt-position + 2, len)
    else: s
    end
  end
end

fun string-to-number-i(s):
  cases(Option) string-to-number(s):
  | some(n) => n
  | none => -1e100
  end
end

fun get-girth(n):
  num-floor(log-base(10, num-abs(n)))
end

fun make-sci(underlying-num, underlying-num-str, max-chars) block:
  # spy "make-sci": underlying-num, underlying-num-str, max-chars end
  u-len = string-length(underlying-num-str)
  girth = num-floor(log-base(10, num-abs(underlying-num)))
  neg-girth = 0 - girth
  # spy 'girth': girth, neg-girth end
  decimal-point-position = string-index-of(underlying-num-str, '.')
  int-str = if decimal-point-position > -1:
    string-substring(underlying-num-str, 0, decimal-point-position)
    else: underlying-num-str
    end
  dec-str = if decimal-point-position > -1:
    string-substring(underlying-num-str, decimal-point-position + 1, u-len)
    else: ''
    end
  # spy: int-str, dec-str end
  dec-str-len = string-length(dec-str)
  int-part = if (girth > 0) and (girth < max-chars): int-str + '.'
    else if girth >= 0:
    string-substring(int-str, 0, 1) + '.'
    else: string-substring(dec-str, neg-girth - 1, neg-girth) + '.'
    end
  dec-part = if (girth > 0) and (girth < max-chars): dec-str
    else if girth >= 0:
    string-substring(int-str, 1, string-length(int-str)) +
                dec-str
    else if neg-girth == dec-str-len: '0'
    else: string-substring(dec-str, neg-girth, dec-str-len)
    end
  expt-part = if (girth > 0) and (girth < max-chars): ''
              else if girth == 0: ''
              else if girth > 0: 'e' + num-to-string(girth)
              else: 'e-' + num-to-string(neg-girth)
              end
  # spy: int-part, dec-part, expt-part end

  if (string-length(int-part) +
     string-length(dec-part) + string-length(expt-part)) <= max-chars:
     # spy: fixme: 100 end
     int-part + dec-part + expt-part
  else:
    # spy: fixme: 101 end
     shrink-dec(int-part + dec-part + expt-part, max-chars)
  end
end

fun make-unsci(underlying-num-str, u-len):
  # spy 'make-unsci of': underlying-num-str end
  e-position = string-index-of(underlying-num-str, 'e')
  mantissa-str = string-substring(underlying-num-str, 0, e-position)
  exponent = string-to-number-i(string-substring(
    underlying-num-str, e-position + 1, u-len))
  mantissa-len = string-length(mantissa-str)
  mantissa-decimal-point-position = string-index-of(mantissa-str, '.')
  mantissa-int-str = if mantissa-decimal-point-position > -1:
      string-substring(mantissa-str, 0, mantissa-decimal-point-position)
    else: mantissa-str
    end
  mantissa-frac-str = if mantissa-decimal-point-position > -1:
    string-substring(mantissa-str,
      mantissa-decimal-point-position + 1, mantissa-len)
    else: ''
    end
  if exponent == 0:
    underlying-num-str
  else if exponent > 0:
    mantissa-frac-len = string-length(mantissa-frac-str)
    if mantissa-frac-len == exponent:
       mantissa-int-str + mantissa-frac-str
    else if mantissa-frac-len < exponent:
       mantissa-int-str + mantissa-frac-str +
        string-repeat('0', exponent - mantissa-frac-len)
    else:
       mantissa-int-str +
        string-substring(mantissa-frac-str, 0, exponent) + '.' +
        string-substring(mantissa-frac-str, exponent, mantissa-frac-len)
    end
  else:
    shadow exponent = 0 - exponent
    mantissa-int-len = string-length(mantissa-int-str)
    if mantissa-int-len == exponent:
       "0." + mantissa-int-str + mantissa-frac-str
    else if mantissa-int-len < exponent:
       "0." + string-repeat('0', (exponent - mantissa-int-len) - 1) +
      mantissa-int-str + mantissa-frac-str
    else:
      string-substring(mantissa-int-str, 0, mantissa-int-len - exponent) +
      "." +
      string-substring(mantissa-int-str, mantissa-int-len - exponent,
      mantissa-int-len)
    end
  end
end

fun make-zero-string(n):
  fold(lam(acc, _): acc + '0' end, '', L.range(0, n))
end

fun shrink-dec-part(dec-part, max-chars) block:
  dec-part-len = string-length(dec-part)
  girth = get-girth(string-to-number-i(dec-part))
  left-0-padding = make-zero-string(dec-part-len - (girth + 1))
  var ss1n = string-to-number-i(string-substring(dec-part, 0, max-chars))
  ss2n = string-to-number-i(string-substring(dec-part, max-chars, max-chars + 1))
  # spy: sdp-fixme: 1, dec-part, max-chars, ss1n, ss2n end
  if ss2n >= 5: ss1n := ss1n + 1 else: false end
  left-0-padding + num-to-string(ss1n)
end

fun shrink-dec(num-str, max-chars):
  # spy 'shrink-dec of': num-str, max-chars end
  len = string-length(num-str)
  if len == max-chars: num-str
  else:
    decimal-position = string-index-of(num-str, '.')
    if ((decimal-position + 1) == max-chars) block:
      var digit-after-point = 0
      if max-chars < len:
        digit-after-point := string-to-number-i(string-substring(num-str, decimal-position + 1, decimal-position + 2))
      else: false
      end
      var wholenum = string-to-number-i(string-substring(num-str, 0, decimal-position))
      if digit-after-point >= 5:
        wholenum := wholenum + 1
      else: false
      end
      num-to-string(wholenum)
    else if decimal-position <= max-chars:
      # spy: shrink-dec-fixme: 2 end
      int-part = string-substring(num-str, 0, decimal-position)
      int-part-len = string-length(int-part)
      dec-expt-part = string-substring(num-str, decimal-position + 1, len)
      expt-position = string-index-of(dec-expt-part, 'e')
      if expt-position == -1:
        dec-part-mod = shrink-dec-part(dec-expt-part, max-chars - (int-part-len + 1))
        int-part + '.' + dec-part-mod
      else:
        # spy: shrink-dec-fixme: 2.1 end
        # spy: int-part, dec-expt-part end
        dec-expt-part-len = string-length(dec-expt-part)
        dec-part = string-substring(dec-expt-part, 0, expt-position)
        expt-part = string-substring(dec-expt-part, expt-position, dec-expt-part-len)
        # spy: dec-part, expt-part end
        dec-part-len = string-length(dec-part)
        expt-part-len = string-length(expt-part)
        dec-max-chars = max-chars - (int-part-len + expt-part-len + 1)
        # spy: int-part-len, dec-part-len, expt-part-len, dec-max-chars end
        if dec-part-len <= dec-max-chars:
          num-str
        else:
          dec-part-mod = shrink-dec-part(dec-part, dec-max-chars)
          int-part + '.' + dec-part-mod + expt-part
        end
      end
    else:
      # spy: shrink-dec-fixme: 3 end
      num-str
    end
  end
end

fun num-to-sci(n, max-chars) block:
  # spy 'num-to-sci of': n end
  negativep = (n < 0)
  roughp = num-is-roughnum(n)
  underlying-num = if negativep: 0 - n else: n end
  # spy: underlying-num end
  underlying-num-str = fake-num-to-fixnum(underlying-num)
  # spy: underlying-num-str end
  u-len = string-length(underlying-num-str)
  g-len = (if negativep: 1 else: 0 end) + (if roughp: 1 else: 0 end) + u-len
  prefix = (if roughp: '~' else: '' end) + (if negativep: '-' else: '' end)
  max-chars-mod = max-chars - string-length(prefix)
  if not(string-contains(underlying-num-str, 'e')):
    # spy: fixme: 1, g-len, max-chars end
    if g-len <= max-chars:
      if not(string-contains(underlying-num-str, '/') or string-contains(underlying-num-str, '.')):
        # spy: fixme: 1 end
        num-to-string(n)
      else:
        # spy: fixme: 1.1 end
        prefix + underlying-num-str
      end
    else if num-to-fixnum(underlying-num) == 0: prefix + '0'
    else:
      girth = num-floor(log-base(10, num-abs(underlying-num)))
      # spy: fixme: 2, girth, underlying-num-str end
      sci-num-str = make-sci(underlying-num, underlying-num-str,
         max-chars-mod)
      # spy: sci-num-str end
      if (girth < 0) and (girth > -3):
        # spy: fixme: 2.4 end
        prefix + shrink-dec(underlying-num-str, max-chars-mod)
      else if string-length(sci-num-str) <= max-chars-mod:
        # spy: fixme: 2.5 end
        prefix + sci-num-str
      else if not(string-contains(underlying-num-str, '/')):
        # spy: fixme: 2.6 end
        prefix + shrink-dec(underlying-num-str, max-chars-mod)
      else:
        # spy: fixme: 3 end
        prefix + sci-num-str
      end
    end
  else:
    unsci-num-str = prefix + make-unsci(underlying-num-str, u-len)
    # spy "unsci": prefix, underlying-num-str, unsci-num-str, g-len, max-chars end
    # spy: unsci-num-str-len: string-length(unsci-num-str) end
    if string-length(unsci-num-str) <= max-chars: unsci-num-str
    else if g-len <= max-chars: prefix + underlying-num-str
    else:
      # spy: fixme: 4 end
      prefix + shrink-dec(underlying-num-str, max-chars)
    end
  end
where:

  num-to-sci(0.00000343, 10) is "0.00000343" # max fixnum size (small)
  num-to-sci(0.000000343, 11) is "0.00000343"
  num-to-sci(0.00000343, 8) is "3.43e-6"
  num-to-sci(0.00000343, 9) is "3.43e-6"
  num-to-sci(4564634745675734, 16) is "4564634745675734" # max fixnum size (big)
  num-to-sci(45646347456757342, 17) is "45646347456757342"
  num-to-sci(45646347456757342, 16) is "4.56463474568e16"
  num-to-sci(4564634745675734, 15) is "4.5646347457e15"
  num-to-sci(-45646347456757342.000343, 16) is "-4.5646347457e16"
  num-to-sci(0.000001, 8) is "0.000001"
  num-to-sci(-0.000001, 8) is "-1.0e-6"
  num-to-sci(1/3, 18) is "0.3333333333333333"
  num-to-sci(1/3, 19) is "0.3333333333333333" # extra char is unused due to fixnum precision
  num-to-sci(1/3, 8) is "0.333333"
  num-to-sci(1 + 1/3, 8) is "1.333333"
  num-to-sci(2.712828, 7) is "2.71283" # rounding
  num-to-sci(3.1415962, 8) is "3.141596" # rounding
  num-to-sci(0.011238, 7) is "0.01124" # not 0.01123
  num-to-sci(12387691745124903567102, 7) is "1.24e22" # not 1.23876
  num-to-sci(0.0000000000456, 7) is "4.6e-11" # not 4.56e-1
  num-to-sci(203.680147, 9) is "203.68015" # not 2.0368e2
  num-to-sci(103.40123123,9) is "103.40123" # not 1.0340e2
  num-to-sci(20368014712358, 9) is "2.0368e13"

  num-to-sci(20368.0147, 9) is "20368.015"
  num-to-sci(203680.147, 9) is "203680.15"
  num-to-sci(2036801.47, 9) is "2036801.5"
  num-to-sci(20368014.7, 9) is "20368015" # "2.03680e7"

  num-to-sci(0.00001284567, 8) is "1.285e-5" # "0.00001"
  num-to-sci(0.00001284567, 9) is "1.2846e-5" # "0.000013"
  num-to-sci(0.00001234567, 7) is "1.23e-5" # "1.2e-5"
  num-to-sci(0.000001239567, 8) is "1.240e-6"

end
# print(num-to-sci(23e3, 18))


fun easy-num-repr(n, max-chars) block:
  negativep = (n < 0)
  roughp = num-is-roughnum(n)
  prefix = (if roughp: '~' else: '' end) + (if negativep: '-' else: '' end)
  prefix-len = string-length(prefix)
  max-chars-mod = max-chars # - prefix-len
  underlying-num = if negativep: 0 - n else: n end
  underlying-num-str = fake-num-to-fixnum(underlying-num)
  decimal-point-position = string-index-of(underlying-num-str, '.')
  underlying-num-str-len = string-length(underlying-num-str)
  # spy: underlying-num, underlying-num-str, underlying-num-str-len end
  var int-str = underlying-num-str
  var dec-str = ''
  if decimal-point-position > -1 block:
    int-str := string-substring(underlying-num-str, 0, decimal-point-position)
    dec-str := '0' + string-substring(underlying-num-str, decimal-point-position, underlying-num-str-len)
  else: false
  end
  # spy: int-str, dec-str end
  var output = ''
  if underlying-num == 1 block: prefix + '1'
  else:
    var len-2 = 0
    if underlying-num > 1:
      len-2 := string-length(int-str)
    else:
      len-2 := (0 - get-girth(underlying-num)) + 2
    end
    # spy: len-2, max-chars-mod end
    if len-2 <= max-chars-mod block:
      # spy: fixme: 'ez' end
      if len-2 < max-chars-mod: len-2 := len-2 + 1 else: false end
        # spy: len-2, decimal-point-position end
      if (len-2 - 1) == decimal-point-position: len-2 := len-2 + 1 else: false end
      num-2 = string-substring(underlying-num-str, 0, len-2)
      # spy: len-2, num-2 end
      output := prefix + num-to-sci(string-to-number-i(num-2), max-chars-mod)
    else: output := num-to-sci(n, max-chars)
    end
    output
  end
  where:
    easy-num-repr(0.0001234, 6) is "0.0001"
    easy-num-repr(2343.234, 6) is "2343.2"
    easy-num-repr(0.000000001234, 6) is "1.2e-9"
    easy-num-repr(2343243432.234, 6) is "2.34e9"
end

# fun t():
#     [list: easy-num-repr(2343.234, 6), "2343.2"]
#   # [list: easy-num-repr(0.0001234, 6), "0.0001"]
#   # [list: num-to-sci(20368014.7, 9),  "20368014"]
#   # [list: num-to-sci(0.00001234567, 7), "1.2e-5"]
# end

# num-to-sci(203.680147,9) should evaluate to ~203.6801 instead of ~2.0368e2
