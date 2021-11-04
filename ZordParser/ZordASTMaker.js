import antlr4 from 'antlr4'
import ZordLexer from './ZordLexer.js'
import ZordParser from './ZordParser.js'
import ZordParserVisitor from './ZordParserVisitor.js'
import { default as AST } from '../src/CP/Syntax/Source.purs'
import { default as OP } from '../src/CP/Syntax/Common.purs'
import { default as Either } from '../.spago/either/v5.0.0/src/Data/Either.purs'
import { default as Maybe } from '../.spago/maybe/v5.0.0/src/Data/Maybe.purs'
import { default as Tuple } from '../.spago/tuples/v6.0.1/src/Data/Tuple.purs'
import { default as List } from '../.spago/lists/v6.0.1/src/Data/List/Types.purs'

export default class ZordASTMaker extends ZordParserVisitor {

    // Convert array to list
    listify(array) {
        let list = List.Nil.value;
        for (let each of array.reverse()){
            list = new List.Cons(each, list);
        }
        return list;
    }


    // Visit a parse tree produced by ZordParser#program.
	visitProgram(ctx) {
        const expression = ctx.expression();
        const definitions = ctx.definition();
        let program = this.visitExpression(expression);
        for(let i = definitions.length - 1; i>=0; i--){
            program = this.visitDefinition(definitions[i], program);
        }
        return program;
    } 
  
  
    // Visit a parse tree produced by ZordParser#open.
    visitOpen(ctx) {
        return null;
    }
  
  
    // Visit a parse tree produced by ZordParser#definition.
    visitDefinition(ctx, program) {
        const typeDef = ctx.typeDef();
        const termDef = ctx.termDef();
        if(typeDef !== null)
            return this.visitTypeDef(typeDef, program);
        else
            return this.visitTermDef(termDef, program);
    }
  
  
    // Visit a parse tree produced by ZordParser#typeDef.
    visitTypeDef(ctx, p) {
        const typeNameDecls = ctx.typeNameDecl();
        const angleTNDCount = ctx.Less().length;
        const type = ctx.type();
        const a = this.visitTypeNameDecl(typeNameDecls[0]);
        const sorts = this.listify(typeNameDecls.splice(1, angleTNDCount+1).map(this.visitTypeNameDecl, this));
        const parms = this.listify(typeNameDecls.splice(angleTNDCount + 1).map(this.visitTypeNameDecl, this));
        const t = this.visitType(type);
        return new AST.TmType(a, sorts, parms, t, p);
    }
  
  
    // Visit a parse tree produced by ZordParser#termDef.
    visitTermDef(ctx, p) {
        const x = this.visitTermNameDecl(ctx.termNameDecl());
        const tys = this.listify(ctx.typeParam().map(this.visitTypeParam, this));
        const tms = this.listify(ctx.termParam().map(this.visitTermParam, this));
        const t = ctx.type() === null ? Maybe.Nothing.value : new Maybe.Just(this.visitType(ctx.type()));
        const e = this.visitExpression(ctx.expression());
        return new AST.TmDef(x, tys, tms, t, e, p);
    }


    // Visit a parse tree produced by ZordParser#type.
    visitType(ctx) {
        if (ctx.btype() !== null) {
            return this.visitBtype(ctx.btype());
        } else if (ctx.Intersect() !== null) {
            return new AST.TyAnd(this.visitType(ctx.type(0)), this.visitType(ctx.type(0)));
        } else if (ctx.Arrow() !== null) {
            return new AST.TyArrow(this.visitType(ctx.type(0)), this.visitType(ctx.type(0)));
        } else {
            console.error("Error at type");
        }
    }
  
  
    // Visit a parse tree produced by ZordParser#btype.
    visitBtype(ctx) {
        if (ctx.ForAll() !== null) {
            return new AST.TyForall(this.listify(ctx.typeParam().map(this.visitTypeParam, this)), this.visitType(ctx.type(0)));
        }
        else if (ctx.TraitCaps() !== null){
            if (ctx.TraitArrow() === null){
                const ti = Maybe.Nothing.value;
                const to = this.visitType(ctx.type(0));
                return new AST.TyTrait(ti, to);
            } else {
                const ti = new Maybe.Just(this.visitType(ctx.type(0)));
                const to = this.visitType(ctx.type(1));
                return new AST.TyTrait(ti, to);
            };
        } else if (ctx.Mu() !== null) {
            return new AST.TyRec(
                this.visitTypeNameDecl(ctx.typeNameDecl()),
                this.visitType(ctx.type())
            );
        } else {
            let btype = this.visitAtype(ctx.getChild(0));
            for(let i=1; i<ctx.getChildCount();i++){
                const child = ctx.getChild(i);
                if (child.ruleIndex === undefined){
                    continue;
                } else if (child.ruleIndex === ZordParser.RULE_sort){
                    btype = new AST.TyApp(btype, this.visitSort(child));
                } else if (child.ruleIndex === ZordParser.RULE_atype){
                    btype = new AST.TyApp(btype, this.visitAtype(child));
                } else {
                    console.error("Error at btype");
                }
            }
            return btype;
        }
    }


    // Visit a parse tree produced by ZordParser#atype.
	visitAtype(ctx) {
        if (ctx.getChild(0).symbol === undefined){
            switch (ctx.getChild(0).ruleIndex) {
                case ZordParser.RULE_typeName:
                    return this.visitTypeName(ctx.typeName());
                case ZordParser.RULE_recordType:
                    return this.visitRecordType(ctx.recordType());
                default:
                    console.error("Error at Atype");
            }
        } else {
            switch (ctx.getChild(0).symbol.type) {
                case ZordParser.Int :
                    return AST.TyInt.value;
                case ZordParser.Double :
                    return AST.TyDouble.value;
                case ZordParser.Bool :
                    return AST.TyBool.value;
                case ZordParser.StringType :
                    return AST.TyString.value;
                case ZordParser.Top :
                    return AST.TyTop.value;
                case ZordParser.Bot :
                    return AST.TyBot.value;
                case ZordParser.BracketOpen :
                    return new AST.TyArray(
                        this.visitType(ctx.type())
                    );
                case ZordParser.ParenOpen :
                    return this.visitType(ctx.type());
                default:
                    console.error("Error at Atype");
            }
        }
    }
  
  
    // Visit a parse tree produced by ZordParser#recordType.
    visitRecordType(ctx) {
        return new AST.TyRcd(this.listify(ctx.recordTypeElement().map(this.visitRecordTypeElement, this)));
    }

    // Visit a parse tree produced by ZordParser#recordTypeElement.
	visitRecordTypeElement(ctx) {
        return new AST.RcdTy(
            this.visitLabelDecl(ctx.labelDecl()),
            this.visitType(ctx.type()),
            ctx.Question() !== null
        );
    }


    // Visit a parse tree produced by ZordParser#expression.
    visitExpression(ctx) {
        const position = {line: ctx.start.line, column: ctx.start.column};
        const opexpr = this.visitOpexpr(ctx.opexpr());
        let colonexpr = null;
        if (ctx.Colon() !== null) {
            colonexpr = new AST.TmAnno(
                opexpr,
                this.visitType(ctx.type())
            );
        } else if (ctx.Backslash() !== null) {
            colonexpr = new AST.TmExclude(
                opexpr,
                this.visitType(ctx.type())
            );
        } else {
            colonexpr = opexpr;
        }
        return new AST.TmPos(position, colonexpr);
    }

    // Visit a parse tree produced by ZordParser#opexpr.
	visitOpexpr(ctx) {
        const count = ctx.getChildCount();
        let op = null
        switch (count) {
            case 1:
                return this.visitLexpr(ctx.lexpr());
            case 2:
                const opexpr = this.visitOpexpr(ctx.opexpr(0));
                switch (ctx.getChild(0).symbol.type) {
                    case ZordParser.Minus:
                        op = OP.Neg.value;
                        break;
                    case ZordParser.Not:
                        op = OP.Not.value;
                        break;
                    case ZordParser.Length:
                        op = OP.Len.value;
                        break;
                    default:
                        console.error("Error at Unary Opexpr");
                }
                return new AST.TmUnary(op, opexpr);
            default:
                const opexpr1 = this.visitOpexpr(ctx.opexpr(0));
                const opexpr2 = this.visitOpexpr(ctx.opexpr(1));
                switch (ctx.getChild(1).symbol.type) {
                    case ZordParser.Index:
                        op = OP.Index.value;
                        break;
                    case ZordParser.Modulo:
                        op = new OP.Arith(OP.Mod.value);
                        break;
                    case ZordParser.Divide:
                        op = new OP.Arith(OP.Div.value);
                        break;
                    case ZordParser.Star:
                        op = new OP.Arith(OP.Mul.value);
                        break;
                    case ZordParser.Minus:
                        op = new OP.Arith(OP.Sub.value);
                        break;
                    case ZordParser.Plus:
                        op = new OP.Arith(OP.Add.value);
                        break;
                    case ZordParser.Append:
                        op = OP.Append.value;
                        break;
                    case ZordParser.Less:
                        op = new OP.Comp(OP.Lt.value);
                        break;
                    case ZordParser.Greater:
                        op = new OP.Comp(OP.Gt.value);
                        break;
                    case ZordParser.LessEqual:
                        op = new OP.Comp(OP.Le.value);
                        break;
                    case ZordParser.GreaterEqual:
                        op = new OP.Comp(OP.Ge.value);
                        break;
                    case ZordParser.Equal:
                        op = new OP.Comp(OP.Eql.value);
                        break;
                    case ZordParser.NotEqual:
                        op = new OP.Comp(OP.Neq.value);
                        break;
                    case ZordParser.And:
                        op = new OP.Logic(OP.And.value);
                        break;
                    case ZordParser.Or:
                        op = new OP.Logic(OP.Or.value);
                        break;
                    case ZordParser.Forward:
                        return new AST.TmForward(opexpr1, opexpr2);
                    case ZordParser.Merge:
                        return new AST.TmMerge(opexpr1, opexpr2);
                    default:
                        console.error("Error in Binary Opexpr");
                }
                return new AST.TmBinary(op, opexpr1, opexpr2);
        }

    }

	// Visit a parse tree produced by ZordParser#lexpr.
	visitLexpr(ctx) {
        switch (ctx.getChild(0).ruleIndex) {
            case ZordParser.RULE_fexpr:
                return this.visitFexpr(ctx.fexpr());
            case ZordParser.RULE_lambda:
                return this.visitLambda(ctx.lambda());
            case ZordParser.RULE_bigLambda:
                return this.visitBigLambda(ctx.bigLambda());
            case ZordParser.RULE_let_:
                return this.visitLet_(ctx.let_());
            case ZordParser.RULE_letRec:
                return this.visitLetRec(ctx.letRec());
            case ZordParser.RULE_open_:
                return this.visitOpen_(ctx.open_());
            case ZordParser.RULE_ifElse:
                return this.visitIfElse(ctx.ifElse());
            case ZordParser.RULE_trait:
                return this.visitTrait(ctx.trait());
            case ZordParser.RULE_new_:
                return this.visitNew_(ctx.new_());
            case ZordParser.RULE_toString_:
                return this.visitToString_(ctx.toString_());
            case ZordParser.RULE_fold:
                return this.visitFold(ctx.fold());
            case ZordParser.RULE_unfold:
                return this.visitUnfold(ctx.unfold());
            default:
                console.error("Error in Lexpr");
        }
    }
  
  
    // Visit a parse tree produced by ZordParser#lambda.
    visitLambda(ctx) {
        return new AST.TmAbs(
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitExpression(ctx.expression())
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#bigLambda.
    visitBigLambda(ctx) {
        return new AST.TmTAbs(
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.visitExpression(ctx.expression())
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#let_.
    visitLet_(ctx) {
        return new AST.TmLet(
            this.visitTermNameDecl(ctx.termNameDecl()),
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#letRec.
    visitLetRec(ctx) {
        return new AST.TmLetRec(
            this.visitTermNameDecl(ctx.termNameDecl()),
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitType(ctx.type()),
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#open_.
    visitOpen_(ctx) {
        return new AST.TmOpen(
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#ifElse.
    visitIfElse(ctx) {
        return new AST.TmIf(
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1)),
            this.visitExpression(ctx.expression(2))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#trait.
    visitTrait(ctx) {
        return new AST.TmTrait(
            ctx.selfAnno() === null ? Maybe.Nothing.value : new Maybe.Just(this.visitSelfAnno(ctx.selfAnno())),
            ctx.type() === null ? Maybe.Nothing.value : new Maybe.Just(this.visitType(ctx.type())),
            ctx.opexpr().length === 2 ? new Maybe.Just(ctx.opexpr(0)) : Maybe.Nothing.value,
            ctx.opexpr().length === 2 ? ctx.opexpr(1) : ctx.opexpr(0)
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#new_.
    visitNew_(ctx) {
        return new AST.TmNew(
            this.visitOpexpr(ctx.opexpr())
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#toString_.
    visitToString_(ctx) {
        return new AST.TmToString(
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by ZordParser#fold.
	visitFold(ctx) {
        return new AST.TmFold(
            this.visitAtype(ctx.atype()),
            this.visitDotexpr(ctx.dotexpr())
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#unfold.
    visitUnfold(ctx) {
        return new AST.TmUnfold(
            this.visitAtype(ctx.atype()),
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by ZordParser#fexpr.
    visitFexpr(ctx) {
        const c = ctx.getChild(0);
        let fexpr = undefined;
        let isCtor = undefined;
        switch(c.ruleIndex){
            case ZordParser.RULE_typeNameDecl:
                fexpr = new AST.TmVar(this.visitTypeNameDecl(c));
                isCtor = true;
                break;
            case ZordParser.RULE_dotexpr:
                fexpr = this.visitDotexpr(c);
                isCtor = false;
                break;
            default:
                console.error("Error at Fexpr");
        }
        for(let i = 1; i<ctx.getChildCount(); i++){
            let child = ctx.getChild(i);
            if (child.ruleIndex === undefined){
                continue;
            } else if (child.ruleIndex === ZordParser.RULE_dotexpr) {
                fexpr = new AST.TmApp(fexpr, this.visitDotexpr(child));
            } else if (child.ruleIndex === ZordParser.RULE_atype) {
                fexpr = new AST.TmTApp(fexpr, this.visitAtype(child));
            } else {
                //console.log(child);
                console.error("Error at fexpr");
            }
        }
        if (isCtor)
            new AST.TmNew(fexpr);
        else
            return fexpr;
    }
  
  
    // Visit a parse tree produced by ZordParser#dotexpr.
    visitDotexpr(ctx) {
        let dotexpr = this.visitAexpr(ctx.aexpr());
        for (let i = 0;i<ctx.label().length; i++){
            dotexpr = new AST.TmPrj(dotexpr, this.visitLabel(ctx.label(i)));
        }
        return dotexpr;
    }
  
  
    // Visit a parse tree produced by ZordParser#aexpr.
    visitAexpr(ctx) {
        let child = ctx.getChild(0);
        if (child.ruleIndex === undefined){
            switch (child.symbol.type){
                case ZordParser.Number:
                    let num = child.getText();
                    if (num.includes('.') || num.includes('e') || num.includes('E')){
                        return new AST.TmNumber(parseFloat(num));
                    } else if ('Xx'.includes(num[1])){
                        return new AST.TmInt(parseInt(num.slice(2), 16));
                    } else if ('Oo'.includes(num[1])){
                        return new AST.TmInt(parseInt(num.slice(2), 8));
                    } else {
                        return new AST.TmInt(parseInt(num));
                    }
                case ZordParser.String:
                    return new AST.TmString(child.getText().slice(1,-1));
                case ZordParser.Unit:
                    return AST.TmUnit.value;
                case ZordParser.True_:
                    return new AST.TmBool(true);
                case ZordParser.False_:
                    return new AST.TmBool(false);
                case ZordParser.Undefined_:
                    return AST.TmUndefined.value;
                case ZordParser.Dollar:
                    return new AST.TmVar(this.visitTypeNameDecl(ctx.typeNameDecl()));
                case ZordParser.ParenOpen:
                    return this.visitExpression(ctx.expression());
                default:
                    console.error("error at aexpr");
            }
        } else {
            switch (child.ruleIndex){
                case ZordParser.RULE_termName:
                    return this.visitTermName(ctx.termName());
                case ZordParser.RULE_document:
                    return this.visitDocument(ctx.document());
                case ZordParser.RULE_array:
                    return this.visitArray(ctx.array());
                case ZordParser.RULE_record:
                    return this.visitRecord(ctx.record());
                case ZordParser.RULE_recordUpdate:
                    return this.visitRecordUpdate(ctx.recordUpdate());
                default:
                    console.log(child);
                    console.error("Error at Aexpr");
            }
        }
    }
  
  
    // Visit a parse tree produced by ZordParser#array.
    visitArray(ctx) {
        return new AST.TmArray(
            ctx.expression().map(this.visitExpression, this)
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#record.
    visitRecord(ctx) {
        const record = [];
        for(let i = 0; i<ctx.getChildCount(); i++) {
            let child = ctx.getChild(i);
            if(child.ruleIndex === undefined){
                continue;
            } else {
                switch (child.ruleIndex) {
                    case ZordParser.RULE_recordField:
                        record.push(this.visitRecordField(ctx.recordField()));
                    case ZordParser.RULE_methodPattern:
                        record.push(this.visitMethodPattern(ctx.methodPattern()));
                    case ZordParser.RULE_defaultPattern:
                        record.push(this.visitDefaultPattern(ctx.defaultPattern()));
                    default:
                        console.error("Error in record");
                }
            }
        }
        return new AST.TmRcd(record);
    }
  
  
    // Visit a parse tree produced by ZordParser#recordField.
    visitRecordField(ctx) {
        return new AST.RcdField(
            ctx.Override() !== null,
            this.visitLabelDecl(ctx.labelDecl()),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            new Either.Left(this.visitExpression(ctx.expression()))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#recordUpdate.
    visitRecordUpdate(ctx) {
        const fields = [];
        for (let i=0;i<ctx.labelDecl().length;i++){
            fields.push(new Tuple.Tuple(
                this.visitLabelDecl(ctx.labelDecl(i)),
                this.visitExpression(ctx.expression(i+1))
            ));
        }
        return new AST.TmUpdate(
            new AST.TmUpdate(this.visitExpression(ctx.expression(0)), params)
        )
    }
  
  
    // Visit a parse tree produced by ZordParser#methodPattern.
    visitMethodPattern(ctx) {
        const params = [];
        const params_ = [];
        let j = 0;
        for (let i = 0;i<ctx.getChildCount();i++){
            if(ctx.getChild(i).ruleIndex === ZordParser.RULE_termParam){
                if (j == 0)
                    params.push(this.visitTermParam(ctx.getChild(i)));
                else
                    params_.push(this.visitTermParam(ctx.getChild(i)));
            } else {
                if (i > 0 && ctx.getChild(i-1).ruleIndex === ZordParser.RULE_termParam){
                    j++;
                }
            }
        }
        return new AST.RcdField(
            ctx.Override() !== null,
            this.visitLabelDecl(ctx.labelDecl(0)),
            params,
            new Either.Right(new AST.MethodPattern(
                ctx.selfAnno() === null? Maybe.Nothing.value : new Maybe.Just(this.visitSelfAnno(ctx.selfAnno())),
                this.visitLabelDecl(ctx.labelDecl(1)),
                params_,
                this.visitExpression(ctx.expression())
            ))
        );
    }
  

	// Visit a parse tree produced by ZordParser#defaultPattern.
	visitDefaultPattern(ctx) {
        return new AST.DefaultPattern(
            new AST.MethodPattern(
                ctx.selfAnno() === null? Maybe.Nothing.value : new Maybe.Just(this.visitSelfAnno(ctx.selfAnno())),
                this.visitLabelDecl(ctx.labelDecl()),
                this.listify(ctx.termParam().map(this.visitTermParam, this)),
                this.visitExpression(ctx.expression())
            )
        );
    }

  
    // Visit a parse tree produced by ZordParser#typeParam.
    visitTypeParam(ctx) {
        return new Tuple.Tuple(
            this.visitTypeNameDecl(ctx.typeNameDecl()),
            ctx.type() === null? Maybe.Nothing.value : new Maybe.Just(this.visitType(ctx.type()))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#termParam.
    visitTermParam(ctx) {
        switch (ctx.getChildCount()){
            case 1:
                switch (ctx.getChild(0)){
                    case ZordParser.RULE_termId:
                        return new Tuple.Tuple(
                            this.visitTermId(ctx.termId()),
                            null
                        );
                    case ZordParser.RULE_wildcard:
                        return this.visitWildcard(ctx.wildcard());
                    default:
                        console.error("Error at TermParam");
                }
            case 5:
                return new AST.TmParam(
                    this.visitTermId(ctx.termId()),
                    this.visitType(ctx.type())
                );
            default:
                console.error("Error at TermParam");

        }
    }
  
  
    // Visit a parse tree produced by ZordParser#termId.
    visitTermId(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by ZordParser#wildcard.
    visitWildcard(ctx) {
        const labelDecls = this.listify(ctx.labelDecl().map(this.visitLabelDecl, this));
        const expressions = this.listify(ctx.expression().map(this.visitExpression, this));
        const defaultFields = [];
        for (let i = 0; i<labelDecls.length; i++){
            defaultFields[i] = new Tuple.Tuple(labelDecls[i], expressions[i]);
        }
        return new AST.WildCard(defaultFields);
    }
  
  
    // Visit a parse tree produced by ZordParser#selfAnno.
    visitSelfAnno(ctx) {
        return new Tuple.Tuple(
            this.visitTermNameDecl(ctx.termNameDecl()),
            ctx.type() === null ? Maybe.Nothing.value : new Maybe.Just(this.visitType(ctx.type()))
        );
    }
  
  
    // Visit a parse tree produced by ZordParser#sort.
    visitSort(ctx) {
        if (ctx.TraitArrow() === null){
            const ti = this.visitType(ctx.type(0));
            const to = Maybe.Nothing.value;
            return new AST.TySort(ti, to);
        } else {
            const ti = this.visitType(ctx.type(0));
            const to = new Maybe.Just(this.visitType(ctx.type(1)));
            return new AST.TySort(ti, to);
        };
    }
  
  
    // Visit a parse tree produced by ZordParser#typeNameDecl.
    visitTypeNameDecl(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by ZordParser#typeName.
    visitTypeName(ctx) {
        return new AST.TyVar(ctx.getText());
    }
  
  
    // Visit a parse tree produced by ZordParser#termNameDecl.
    visitTermNameDecl(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by ZordParser#termName.
    visitTermName(ctx) {
        switch (ctx.getChild(0).symbol.type){
            case ZordParser.Lowerid:
                return new AST.TmVar(ctx.getText());
            case ZordParser.Upperid:
                return new AST.TmNew(new AST.TmVar(ctx.getText()));
            default:
                console.error("Error in termName");
        }
    }
  
  
    // Visit a parse tree produced by ZordParser#labelDecl.
    visitLabelDecl(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by ZordParser#label.
    visitLabel(ctx) {
        return ctx.getText();
    }
  

    // Visit a parse tree produced by ZordParser#document.
	visitDocument(ctx) {
        const position = {line: ctx.docElement(0).start.line, column: ctx.docElement(0).start.column};
        const docs = ctx.docElement();
        let foldedDocs = undefined;
        if (docs.length === 0){
            foldedDocs = new AST.TmString("");
        } else {
            foldedDocs = this.visitDocElement(docs[0]);
            for (let each of docs.slice(1))
                foldedDocs = new AST.TmNew(new AST.TmApp(
                    new AST.TmApp(new AST.TmVar("Comp"), foldedDocs),
                    this.visitDocElement(each)
                ));
        }
        return new AST.TmPos(
            position,
            new AST.TmDoc(
                new AST.TmNew(new AST.TmApp(
                    new AST.TmVar("Str"),
                    foldedDocs
                ))
            )
        );
	}


	// Visit a parse tree produced by ZordParser#docElement.
	visitDocElement(ctx) {
        const child = ctx.getChild(0);
        switch (child.ruleIndex){
            case ZordParser.RULE_command:
                return this.visitCommand(child);
            case ZordParser.RULE_interpolation:
                return this.visitInterpolation(child);
            case ZordParser.RULE_newline:
                return this.visitNewline(child);
            case ZordParser.RULE_plaintext:
                return this.visitPlaintext(child);
            default:
                console.error("Error ar DocElement");
        }
	}


	// Visit a parse tree produced by ZordParser#command.
	visitCommand(ctx) {
        const position = {line: ctx.start.line, column: ctx.start.column};
	    const cmd = ctx.getChild(0).getText().slice(1);
        const args = this.listify(ctx.arg().map(this.visitArg, this));
        //foldl
        let folded = new AST.TmVar(cmd);
        for (let arg of args){
            folded = new AST.TmApp(folded, arg)
        }
        if (cmd[0].toUpperCase() === cmd[0]){
            return new AST.TmPos(position, new AST.TmNew(folded));
        } else {
            return new AST.TmPos(position, folded);
        }
	}


	// Visit a parse tree produced by ZordParser#interpolation.
	visitInterpolation(ctx) {
	    return new AST.TmNew(new AST.TmApp(
            new AST.TmVar("Str"),
            new AST.TmToString(this.visitExpression(ctx.expression()))
        ));
	}


	// Visit a parse tree produced by ZordParser#newline.
	visitNewline(ctx) {
        return new AST.TmNew(new AST.TmVar("Endl"));
	}


	// Visit a parse tree produced by ZordParser#plaintext.
	visitPlaintext(ctx) {
        return new AST.TmNew(new AST.TmApp(
            new AST.TmVar("Str"),
            new AST.TmString(ctx.getText())
        ));
	}


	// Visit a parse tree produced by ZordParser#arg.
	visitArg(ctx) {
	    switch(ctx.getChild(0).symbol.type){
            case ZordParser.ParenOpenInTag:
                return this.visitExpression(ctx.expression());
            case ZordParser.BraceOpenInTag:
                return new AST.TmRcd(this.listify(
                    ctx.recordArgField().map(this.visitRecordArgField, this)
                ));
            case ZordParser.BracketOpenInTag:
                return this.visitDocument(ctx);
            default:
                console.error("Error in Arg");
        };
	}


	// Visit a parse tree produced by ZordParser#recordArgField.
	visitRecordArgField(ctx) {
	    const params = listify(ctx.termParam().map(this.visitTermParam, this));
        return new AST.RcdField(
            false,
            this.visitLabelDecl(ctx.labelDecl()),
            params,
            new Either.Left(this.visitExpression(ctx.expression()))
        );
	}

}
