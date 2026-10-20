package arrowSyntax.`macro`

import scala.quoted.{Expr, Quotes, Type, Varargs}

trait ProcMacroStorage[F[_, _], A, B]:
  self: ProcMacro[F, A, B] =>
  import self.q.reflect.*

  private def tupleCompanion(n: Int): Term = Ref(defn.TupleClass(n).companionModule)

  private lazy val tupleXXLCompanion: Term = Ref(Symbol.requiredModule("scala.runtime.TupleXXL"))

  private enum TupleShape:
    case Empty, Single, XXL
    case Small(arity: Int)

  class Storage(
      private val entries: Seq[(sym: Symbol, tpe: TypeRepr)]
  ):
    opaque type Symbols = Seq[Symbol]

    private[Storage] def wrapSymbols(s: Seq[Symbol]): Symbols = s

    private[Storage] def unwrapSymbols(s: Symbols): Seq[Symbol] = s

    private val shape: TupleShape = entries.length match
      case 0           => TupleShape.Empty
      case 1           => TupleShape.Single
      case n if n > 22 => TupleShape.XXL
      case n           => TupleShape.Small(n)

    def isEmpty: Boolean = entries.isEmpty

    def entrySymbols: Seq[Symbol] = entries.map(_.sym)

    def makeSymbols(owner: Symbol): Symbols =
      entries.map(t => Symbol.newBind(owner, Symbol.freshName(t.sym.name), Flags.EmptyFlags, t.tpe))

    /** The symbols of the entries themselves, for trees that are remapped later */
    def entrySymbolsAsSymbols: Symbols = entries.map(_.sym)

    def makeSelect(tuple: Term, index: Int): Term = shape match
      case TupleShape.Empty        => report.errorAndAbort("Cannot select from an empty storage")
      case TupleShape.Single       => tuple
      case TupleShape.Small(arity) => Select.unique(tuple, s"_${index + 1}")
      case TupleShape.XXL          =>
        entries(index).tpe.asType match
          case '[t] =>
            '{ ${ tuple.asExprOf[scala.runtime.TupleXXL] }.productElement(${ Expr(index) }).asInstanceOf[t] }.asTerm

    def makeUnapply(symbols: Symbols): Tree = shape match
      case TupleShape.Empty        => Wildcard()
      case TupleShape.Single       => Bind(symbols.head, Wildcard())
      case TupleShape.Small(arity) =>
        Unapply(
          TypeApply(
            Select.unique(tupleCompanion(arity), "unapply"),
            entries.map(t => Inferred(t.tpe)).toList
          ),
          Nil,
          symbols.map(s => Bind(s, Wildcard())).toList
        )
      case TupleShape.XXL =>
        // TupleXXL elements are untyped, so we need a type test to give the binds their types
        val unchecked = unwrapInlined('{ new scala.unchecked() }.asTerm)
        Unapply(
          Select.unique(tupleXXLCompanion, "unapplySeq"),
          Nil,
          entries
            .zip(symbols)
            .map((t, s) => Bind(s, TypedOrTest(Wildcard(), Inferred(AnnotatedType(t.tpe, unchecked)))))
            .toList
        )

    def makeTupleTerm(symbols: Symbols): Term = shape match
      case TupleShape.Empty        => Literal(UnitConstant())
      case TupleShape.Single       => Ref(symbols.head)
      case TupleShape.Small(arity) =>
        TypeApply(
          Select.unique(tupleCompanion(arity), "apply"),
          entries.map(t => Inferred(t.tpe)).toList
        ).appliedToArgs(symbols.map(s => Ref(s)).toList)
      case TupleShape.XXL =>
        '{ scala.runtime.TupleXXL(${ Varargs(symbols.map(s => Ref(s).asExpr)) }*) }.asTerm

    def makeType: TypeRepr = shape match
      case TupleShape.Empty        => TypeRepr.of[Unit]
      case TupleShape.Single       => entries.head.tpe
      case TupleShape.Small(arity) => defn.TupleClass(arity).typeRef.appliedTo(entries.map(_.tpe).toList)
      case TupleShape.XXL          => TypeRepr.of[scala.runtime.TupleXXL]

    def makePairType(tpe: TypeRepr): TypeRepr =
      if entries.isEmpty then tpe else TypeRepr.of[Tuple2].appliedTo(List(tpe, makeType))

    def makePairUnapply(pat: Tree, tpe: TypeRepr, symbols: Symbols): Tree =
      if entries.isEmpty then pat
      else
        Unapply(
          TypeApply(Select.unique(tupleCompanion(2), "unapply"), List(Inferred(tpe), Inferred(makeType))),
          Nil,
          List(pat, makeUnapply(symbols))
        )

    def makePairTerm(term: Term, tpe: TypeRepr, symbols: Symbols): Term =
      if entries.isEmpty then term
      else
        TypeApply(Select.unique(tupleCompanion(2), "apply"), List(Inferred(tpe), Inferred(makeType)))
          .appliedTo(term, makeTupleTerm(symbols))

    def remap[T <: Tree](tree: T, newSymbols: Symbols, ownerSymbol: Symbol): T =
      val mapping = entries.map(_.sym).zip(newSymbols).toMap

      val mapper = new TreeMap:
        override def transformTerm(tree: Term)(owner: Symbol): Term = tree match
          case Ident(_) if mapping.contains(tree.symbol) => Ref(mapping(tree.symbol))
          case _                                         => super.transformTerm(tree)(owner)

        // TreeMap does not recurse into the pattern of a Bind, so we handle all Binds ourselves
        override def transformTree(tree: Tree)(owner: Symbol): Tree = tree match
          case b @ Bind(name, inner) =>
            Bind(mapping.getOrElse(b.symbol, b.symbol), transformTree(inner)(owner))
          case _ => super.transformTree(tree)(owner)

      mapper.transformTree(tree)(ownerSymbol) match
        case t: Term => t.changeOwner(ownerSymbol).asInstanceOf[T]
        case t       => t.asInstanceOf[T]

    def addStorage(storage: Storage): Storage.CombinedStorage[this.type, storage.type] =
      new Storage.CombinedStorage(this, storage)

    def filter(keep: Symbol => Boolean): Storage.FilteredStorage[this.type] =
      new Storage.FilteredStorage(this, keep)

  object Storage:
    class FilteredStorage[P <: Storage & scala.Singleton](val parent: P, keep: Symbol => Boolean)
        extends Storage(parent.entries.filter(t => keep(t.sym))):
      def filterSymbols(parentSymbols: parent.Symbols): Symbols =
        wrapSymbols(
          parent.entries.zip(parent.unwrapSymbols(parentSymbols)).collect { case (t, s) if keep(t.sym) => s }
        )

    class CombinedStorage[L <: Storage & scala.Singleton, R <: Storage & scala.Singleton](
        val left: L,
        val right: R
    ) extends Storage(left.entries ++ right.entries):
      def addSymbols(leftSymbols: left.Symbols, rightSymbols: right.Symbols): Symbols =
        wrapSymbols(left.unwrapSymbols(leftSymbols) ++ right.unwrapSymbols(rightSymbols))

    def fromPat(pat: PatBinder): Storage = new Storage(Binder.collectSymbolsAndTypes(pat))
