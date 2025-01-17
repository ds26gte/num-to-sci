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

fun fake-num-to-fixnum-no-exp(n):
  make-unsci(fake-num-to-fixnum(n))
end

fun string-to-number-i(s):
  cases(Option) string-to-number(s):
  | some(n) => n
  | none => -1e100
  end
end

fun get-girth(n):
  if n == 0: 0
  else: num-floor(log-base(10, num-abs(n)))
  end
end

fun make-sci(underlying-num, underlying-num-str, max-chars) block:
  # spy "make-sci": underlying-num, underlying-num-str, max-chars end
  underlying-num-str-len = string-length(underlying-num-str)
  girth = num-floor(log-base(10, num-abs(underlying-num)))
  neg-girth = 0 - girth
  # spy 'girth': girth, neg-girth end
  decimal-point-position = string-index-of(underlying-num-str, '.')
  int-str = if decimal-point-position > -1:
    string-substring(underlying-num-str, 0, decimal-point-position)
    else: underlying-num-str
    end
  dec-str = if decimal-point-position > -1:
    string-substring(underlying-num-str, decimal-point-position + 1, underlying-num-str-len)
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

  output = int-part + dec-part + expt-part

  if string-length(output) <= max-chars:
    # spy: fixme: 100 end
    output
  else:
    # spy: fixme: 101 end
    shrink-dec(output, max-chars)
  end
end

fun make-unsci(underlying-num-str):
  # spy 'make-unsci of': underlying-num-str end
  e-position = string-index-of(underlying-num-str, 'e')
  if e-position < 0: underlying-num-str
  else:
    underlying-num-str-len = string-length(underlying-num-str)
    mantissa-str = string-substring(underlying-num-str, 0, e-position)
    exponent = string-to-number-i(string-substring(
    underlying-num-str, e-position + 1, underlying-num-str-len))
    mantissa-len = string-length(mantissa-str)
    mantissa-decimal-point-position = string-index-of(mantissa-str, '.')
    mantissa-int-str =
    if mantissa-decimal-point-position > -1:
      string-substring(mantissa-str, 0, mantissa-decimal-point-position)
    else: mantissa-str
    end
    mantissa-frac-str =
    if mantissa-decimal-point-position > -1:
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
    else: # ie, exponent < 0
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
end

fun shrink-dec-part(dec-part, max-chars) block:
  # spy 'shrink-dec-part of': dec-part, max-chars end
  if max-chars < 0:
    raise("Cannot compress '" + dec-part + "' to " + num-to-string(max-chars) + " chars")
  else: false
  end
  dec-part-len = string-length(dec-part)
  girth = get-girth(string-to-number-i(dec-part))
  var left-0-padding-len = dec-part-len - (girth + 1)
  ss1n-str = string-substring(dec-part, 0, max-chars)
  var ss1n = 0
  var ss1n-girth = -1
  if ss1n-str <> '' block:
    ss1n := string-to-number-i(ss1n-str)
    ss1n-girth := get-girth(ss1n)
  else: false
  end
  orig-ss1n-girth = ss1n-girth
  ss2n = string-to-number-i(string-substring(dec-part, max-chars, max-chars + 1))
  # spy: fixme: 177 end
  # spy: dec-part, max-chars, ss1n, ss2n end
  if ss2n >= 5 block:
    ss1n := ss1n + 1
    ss1n-girth := get-girth(ss1n)
  else: false
  end
  if ss1n-girth > orig-ss1n-girth:
    left-0-padding-len := left-0-padding-len - 1
  else: false
  end
  if left-0-padding-len < 0:
    'overflow'
  else:
    left-0-padding = string-repeat('0', left-0-padding-len)
    left-0-padding + num-to-string(ss1n)
  end
end

fun shrink-dec(num-str, max-chars):
  len = string-length(num-str)
  # spy 'shrink-dec of': num-str, max-chars, len end
  if len <= max-chars block: num-str
  else:
    dot-position = string-index-of(num-str, '.')
    var int-part = '0'
    var frac-expt-part = ''
    var frac-part = ''
    var expt-part = ''
    if dot-position < 0 block:
      e-position = string-index-of(num-str, 'e')
      if e-position < 0 block:
        int-part := num-str
      else:
        int-part := string-substring(num-str, 0, e-position)
        expt-part := string-substring(e-position, len)
      end
    else:
      int-part := string-substring(num-str, 0, dot-position)
      frac-expt-part := string-substring(num-str, dot-position + 1, len)
      e-position = string-index-of(frac-expt-part, 'e')
      if e-position < 0 block:
        frac-part := frac-expt-part
      else:
        frac-expt-part-len = string-length(frac-expt-part)
        frac-part := string-substring(frac-expt-part, 0, e-position)
        expt-part := string-substring(frac-expt-part, e-position, frac-expt-part-len)
      end
    end
    # spy: int-part, frac-part, expt-part end
    int-part-len = string-length(int-part)
    frac-part-len = string-length(frac-part)
    expt-part-len = string-length(expt-part)
    int-part-num = string-to-number-i(int-part)
    var output = ''
    if int-part-len <= max-chars block:
      if expt-part-len == 0 block:
        if frac-part-len == 0:
          output := int-part
        else:
          # spy: fixme: 302 end
          frac-part-mod = shrink-dec-part(frac-part,
          max-chars - (int-part-len + 1))
          # spy: frac-part-mod end
          if frac-part-mod == 'overflow':
            output := num-to-string(int-part-num + 1)
          else if frac-part-mod == '':
            output := int-part
          else:
            output := int-part + '.' + frac-part-mod
          end
        end
      else:
        var int-dec-part = ''
        frac-part-mod = shrink-dec-part(frac-part,
        max-chars - (int-part-len + expt-part-len + 1))
        if frac-part-mod == 'overflow':
          int-dec-part := num-to-string(int-part-num + 1)
        else if frac-part-mod == '':
          int-dec-part := int-part
        else:
          int-dec-part := int-part + '.' + frac-part-mod
        end
        output := int-dec-part + expt-part
      end
      # spy 'shrink-dec returned': output end
      output
    else:
      raise('shrink-dec: Could not fit ' + num-str + ' into ' +
      num-to-string(max-chars) + ' chars')
    end
  end
end

fun num-to-sci(n, max-chars) block:
  # spy 'num-to-sci of': n, max-chars end
  negativep = (n < 0)
  roughp = num-is-roughnum(n)
  var underlying-num = if negativep: 0 - n else: n end
  # spy: underlying-num end
  underlying-num-str = fake-num-to-fixnum(underlying-num)
  if roughp:
    underlying-num := string-to-number-i(underlying-num-str)
  else: false
  end
  # spy: underlying-num-str end
  underlying-num-str-len = string-length(underlying-num-str)
  prefix = (if roughp: '~' else: '' end) + (if negativep: '-' else: '' end)
  prefix-len = string-length(prefix)
  max-chars-mod = max-chars - prefix-len
  if not(string-contains(underlying-num-str, 'e')):
    # spy: fixme: 1, max-chars-mod end
    if underlying-num-str-len <= max-chars-mod:
      if not(string-contains(underlying-num-str, '/') or string-contains(underlying-num-str, '.')):
        # this weird special case bc of bigints
        # spy: fixme: 1 end
        num-to-string(n)
      else:
        # spy: fixme: 1.1 end
        prefix + underlying-num-str
      end
    else if underlying-num == 0: prefix + '0'
    else:
      girth = num-floor(log-base(10, num-abs(underlying-num)))
      sci-num-str = make-sci(underlying-num, underlying-num-str,
         max-chars-mod)
      # spy: fixme: 2, girth, underlying-num-str, sci-num-str, max-chars-mod end
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
    unsci-underlying-num-str = make-unsci(underlying-num-str)
    # spy "unsci": prefix, underlying-num-str, unsci-underlying-num-str,  max-chars-mod end
    # spy: unsci-num-str-len: string-length(unsci-underlying-num-str) end
    if string-length(unsci-underlying-num-str) <= max-chars-mod:
      prefix + unsci-underlying-num-str
    else if underlying-num-str-len <= max-chars-mod:
      prefix + underlying-num-str
    else:
      # spy: fixme: 4 end
      prefix + shrink-dec(underlying-num-str, max-chars-mod)
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

  num-to-sci(0.0999999, 5) is "0.100"
  num-to-sci(0.9999999, 5) is "1"

  num-to-sci(9999.99, 3) raises "Cannot compress"
end
# print(num-to-sci(23e3, 18))


fun easy-num-repr(n, max-chars) block:
  # spy 'easy-num-repr of': n, max-chars end
  negativep = (n < 0)
  roughp = num-is-roughnum(n)
  prefix = (if roughp: '~' else: '' end) + (if negativep: '-' else: '' end)
  prefix-len = string-length(prefix)
  max-chars-mod = max-chars - prefix-len
  var underlying-num = if negativep: 0 - n else: n end
  underlying-num-str = fake-num-to-fixnum-no-exp(underlying-num)
  if roughp:
    underlying-num := string-to-number-i(underlying-num-str)
  else: false
  end
  decimal-point-position = string-index-of(underlying-num-str, '.')
  underlying-num-str-len = string-length(underlying-num-str)
  # spy: underlying-num, underlying-num-str, underlying-num-str-len, max-chars-mod end
  var int-str = underlying-num-str
  var dec-str = ''
  if decimal-point-position > -1 block:
    int-str := string-substring(underlying-num-str, 0, decimal-point-position)
    dec-str := '0' + string-substring(underlying-num-str, decimal-point-position, underlying-num-str-len)
  else: false
  end
  # spy: int-str, dec-str end
  var output = ''
  if underlying-num == 1 block:
    output := '1'
  else:
    var min-len-needed = 0
    if underlying-num > 1:
      min-len-needed := string-length(int-str)
    else:
      min-len-needed := (0 - get-girth(underlying-num)) + 2
    end
    # spy: min-len-needed, underlying-num-str-len, max-chars-mod end
    if (min-len-needed <= underlying-num-str-len) and (min-len-needed <= max-chars-mod) and (max-chars-mod <= underlying-num-str-len) block:
      # spy: fixme: 'ez' end
      var rounding-check-p = false
      if max-chars-mod == underlying-num-str-len:
        output := string-substring(underlying-num-str, 0, max-chars-mod)
      else:
        var num-2 = string-substring(underlying-num-str, 0, max-chars-mod + 1)
        if underlying-num > 1:
          output := num-to-sci(string-to-number-i(num-2), max-chars-mod)
        else:
          dec-part-mod = shrink-dec-part(string-substring(num-2, 2, string-length(num-2)), max-chars-mod - 2)
          if dec-part-mod == 'overflow':
            output := '1'
          else:
            output := '0.' + dec-part-mod
          end
        end
      end
    else:
      output := num-to-sci(underlying-num, max-chars)
    end
  end
  prefix + output
where:
  easy-num-repr(0.0001234, 6) is "0.0001"
  easy-num-repr(2343.234, 6) is "2343.2"
  easy-num-repr(0.000000001234, 6) is "1.2e-9"
  easy-num-repr(2343243432.234, 6) is "2.34e9"
  easy-num-repr(~0.082805, 9) is "~0.082805"
  easy-num-repr(0.0999999, 5) is "0.100"
  easy-num-repr(0.9999999, 5) is "1"
  easy-num-repr(9999.99, 3) raises "Cannot compress"
end

# fun t():
#   # easy-num-repr(0.0001234, 6)
#   # [list: easy-num-repr(2343.234, 6), "2343.2"]
#   # [list: easy-num-repr(0.000000001234, 6) , 0.000000001234, 6, "1.2e-9"]
#   # [list: easy-num-repr(0.0001234, 6) , "0.0001"]
#   num-to-sci(20368014.7, 9) # "20368015"
#   # num-to-sci(100000, 2)
#   # easy-num-repr(~0.082805, 9)
#   # [list: shrink-dec("0.9999999", 5), shrink-dec-part("99999999", 3)]
#   # num-to-sci(0.099999, 5)
#   # easy-num-repr(0.099999,5)
#   # [list: easy-num-repr(0.0001234, 6), "0.0001"]
#   # [list: num-to-sci(20368014.7, 9), "20368014"]
#   # [list: num-to-sci(0.00001234567, 7), "1.2e-5"]
# end

# num-to-sci(203.680147,9) should evaluate to ~203.6801 instead of ~2.0368e2
