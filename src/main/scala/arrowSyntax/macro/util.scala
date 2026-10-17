package arrowSyntax.`macro`

def indentStructure(s: String, step: String = "  "): String =
  val sb       = StringBuilder()
  var depth    = 0
  var inString = false
  var i        = 0

  def newline() = sb.append('\n').append(step * depth)

  while i < s.length do
    val c = s(i)
    if inString then
      sb.append(c)
      if c == '\\' && i + 1 < s.length then {
        sb.append(s(i + 1));
        i += 1
      } else if c == '"' then inString = false
    else
      c match
        case '"'                                        => inString = true; sb.append(c)
        case '(' if i + 1 < s.length && s(i + 1) == ')' => sb.append("()"); i += 1
        case '('                                        => depth += 1; sb.append('('); newline()
        case ')'                                        => depth -= 1; newline(); sb.append(')')
        case ','                                        =>
          sb.append(',');
          newline();
          if i + 1 < s.length && s(i + 1) == ' ' then
            i +=
              1
        case _ => sb.append(c)
    i += 1
  sb.toString

private def foldBalanced[L, N](leaves: Seq[L])(leaf: L => N)(node: (N, N) => N): N =
  require(leaves.nonEmpty, "Cannot fold an empty sequence")

  if leaves.length == 1 then leaf(leaves.head)
  else
    val (l, r) = leaves.splitAt(leaves.length / 2)
    node(foldBalanced(l)(leaf)(node), foldBalanced(r)(leaf)(node))