import antlr4 from 'antlr4'
import CPnextLexer from './CPnextLexer.js'
import CPnextParser from './CPnextParser.js'
import CPnextParserVisitor from './CPnextParserVisitor.js'
import { default as AST } from '../src/CP/Syntax/Source.purs'
import { default as OP } from '../src/CP/Syntax/Common.purs'
// import { default as Either } from '../.spago/either/v5.0.0/src/Data/Either.purs'
// import { default as Maybe } from '../.spago/maybe/v5.0.0/src/Data/Maybe.purs'
// import { default as Tuple } from '../.spago/tuples/v6.0.1/src/Data/Tuple.purs'
// import { default as List } from '../.spago/lists/v6.0.1/src/Data/List/Types.purs'
import {default as P} from '../src/JSDep.purs'


export default class CPnextASTMaker extends CPnextParserVisitor {

    // Convert array to list
    listify(array) {
        let list = P.Nil.value;
        for (let each of array.reverse()){
            list = new P.Cons(each, list);
        }
        return list;
    }


    // Visit a parse tree produced by CPnextParser#program.
	visitProgram(ctx) {
        const expression = ctx.expression();
        const definitions = ctx.definition();
        let program = this.visitExpression(expression);
        for(let i = definitions.length - 1; i>=0; i--){
            program = this.visitDefinition(definitions[i], program);
        }
        return program;
    } 
  
  
    // Visit a parse tree produced by CPnextParser#open.
    visitOpen(ctx) {
        return null;
    }
  
  
    // Visit a parse tree produced by CPnextParser#definition.
    visitDefinition(ctx, program) {
        const typeDef = ctx.typeDef();
        const termDef = ctx.termDef();
        if(typeDef !== null)
            return this.visitTypeDef(typeDef, program);
        else
            return this.visitTermDef(termDef, program);
    }
  
  
    // Visit a parse tree produced by CPnextParser#typeDef.
    visitTypeDef(ctx, p) {
        const typeNameDecls = ctx.typeNameDecl();
        const angleTNDCount = ctx.Less().length;
        const type = ctx.type();
        const a = this.visitTypeNameDecl(typeNameDecls[0]);
        const sorts = this.listify(typeNameDecls.slice(1, angleTNDCount+1).map(this.visitTypeNameDecl, this));
        const parms = this.listify(typeNameDecls.slice(angleTNDCount + 1).map(this.visitTypeNameDecl, this));
        const t = this.visitType(type);
        return new AST.TmType(a, sorts, parms, t, p);
    }
  
  
    // Visit a parse tree produced by CPnextParser#termDef.
    visitTermDef(ctx, p) {
        const x = this.visitTermNameDecl(ctx.termNameDecl());
        const tys = this.listify(ctx.typeParam().map(this.visitTypeParam, this));
        const tms = this.listify(ctx.termParam().map(this.visitTermParam, this));
        const t = ctx.type() === null ? P.Nothing.value : new P.Just(this.visitType(ctx.type()));
        const e = this.visitExpression(ctx.expression());
        return new AST.TmDef(x, tys, tms, t, e, p);
    }


    // Visit a parse tree produced by CPnextParser#type.
    visitType(ctx) {
        if (ctx.btype() !== null) {
            return this.visitBtype(ctx.btype());
        } else if (ctx.Intersect() !== null) {
            return new AST.TyAnd(this.visitType(ctx.type(0)), this.visitType(ctx.type(1)));
        } else if (ctx.Arrow() !== null) {
            return new AST.TyArrow(this.visitType(ctx.type(0)), this.visitType(ctx.type(1)));
        } else {
            console.error("Error at type");
        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#btype.
    visitBtype(ctx) {
        if (ctx.ForAll() !== null) {
            return new AST.TyForall(this.listify(ctx.typeParam().map(this.visitTypeParam, this)), this.visitType(ctx.type(0)));
        }
        else if (ctx.TraitCaps() !== null){
            if (ctx.TraitArrow() === null){
                const ti = P.Nothing.value;
                const to = this.visitType(ctx.type(0));
                return new AST.TyTrait(ti, to);
            } else {
                const ti = new P.Just(this.visitType(ctx.type(0)));
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
                } else if (child.ruleIndex === CPnextParser.RULE_sort){
                    btype = new AST.TyApp(btype, this.visitSort(child));
                } else if (child.ruleIndex === CPnextParser.RULE_atype){
                    btype = new AST.TyApp(btype, this.visitAtype(child));
                } else {
                    console.error("Error at btype");
                }
            }
            return btype;
        }
    }


    // Visit a parse tree produced by CPnextParser#atype.
	visitAtype(ctx) {
        if (ctx.getChild(0).symbol === undefined){
            switch (ctx.getChild(0).ruleIndex) {
                case CPnextParser.RULE_typeName:
                    return this.visitTypeName(ctx.typeName());
                case CPnextParser.RULE_recordType:
                    return this.visitRecordType(ctx.recordType());
                default:
                    console.error("Error at Atype");
            }
        } else {
            switch (ctx.getChild(0).symbol.type) {
                case CPnextParser.Int :
                    return AST.TyInt.value;
                case CPnextParser.Double :
                    return AST.TyDouble.value;
                case CPnextParser.Bool :
                    return AST.TyBool.value;
                case CPnextParser.StringType :
                    return AST.TyString.value;
                case CPnextParser.Top :
                    return AST.TyTop.value;
                case CPnextParser.Bot :
                    return AST.TyBot.value;
                case CPnextParser.BracketOpen :
                    return new AST.TyArray(
                        this.visitType(ctx.type())
                    );
                case CPnextParser.ParenOpen :
                    return this.visitType(ctx.type());
                default:
                    console.error("Error at Atype");
            }
        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#recordType.
    visitRecordType(ctx) {
        return new AST.TyRcd(this.listify(ctx.recordTypeElement().map(this.visitRecordTypeElement, this)));
    }

    // Visit a parse tree produced by CPnextParser#recordTypeElement.
	visitRecordTypeElement(ctx) {
        return new AST.RcdTy(
            this.visitLabelDecl(ctx.labelDecl()),
            this.visitType(ctx.type()),
            ctx.Question() !== null
        );
    }


    // Visit a parse tree produced by CPnextParser#expression.
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

    // Visit a parse tree produced by CPnextParser#opexpr.
	visitOpexpr(ctx) {
        const count = ctx.getChildCount();
        let op = null
        switch (count) {
            case 1:
                return this.visitLexpr(ctx.lexpr());
            case 2:
                const opexpr = this.visitOpexpr(ctx.opexpr(0));
                switch (ctx.getChild(0).symbol.type) {
                    case CPnextParser.Minus:
                        op = OP.Neg.value;
                        break;
                    case CPnextParser.Not:
                        op = OP.Not.value;
                        break;
                    case CPnextParser.Length:
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
                    case CPnextParser.Index:
                        op = OP.Index.value;
                        break;
                    case CPnextParser.Modulo:
                        op = new OP.Arith(OP.Mod.value);
                        break;
                    case CPnextParser.Divide:
                        op = new OP.Arith(OP.Div.value);
                        break;
                    case CPnextParser.Star:
                        op = new OP.Arith(OP.Mul.value);
                        break;
                    case CPnextParser.Minus:
                        op = new OP.Arith(OP.Sub.value);
                        break;
                    case CPnextParser.Plus:
                        op = new OP.Arith(OP.Add.value);
                        break;
                    case CPnextParser.Append:
                        op = OP.Append.value;
                        break;
                    case CPnextParser.Less:
                        op = new OP.Comp(OP.Lt.value);
                        break;
                    case CPnextParser.Greater:
                        op = new OP.Comp(OP.Gt.value);
                        break;
                    case CPnextParser.LessEqual:
                        op = new OP.Comp(OP.Le.value);
                        break;
                    case CPnextParser.GreaterEqual:
                        op = new OP.Comp(OP.Ge.value);
                        break;
                    case CPnextParser.Equal:
                        op = new OP.Comp(OP.Eql.value);
                        break;
                    case CPnextParser.NotEqual:
                        op = new OP.Comp(OP.Neq.value);
                        break;
                    case CPnextParser.And:
                        op = new OP.Logic(OP.And.value);
                        break;
                    case CPnextParser.Or:
                        op = new OP.Logic(OP.Or.value);
                        break;
                    case CPnextParser.Forward:
                        return new AST.TmForward(opexpr1, opexpr2);
                    case CPnextParser.Merge:
                        return new AST.TmMerge(opexpr1, opexpr2);
                    default:
                        console.error("Error in Binary Opexpr");
                }
                return new AST.TmBinary(op, opexpr1, opexpr2);
        }

    }

	// Visit a parse tree produced by CPnextParser#lexpr.
	visitLexpr(ctx) {
        switch (ctx.getChild(0).ruleIndex) {
            case CPnextParser.RULE_fexpr:
                return this.visitFexpr(ctx.fexpr());
            case CPnextParser.RULE_lambda:
                return this.visitLambda(ctx.lambda());
            case CPnextParser.RULE_bigLambda:
                return this.visitBigLambda(ctx.bigLambda());
            case CPnextParser.RULE_let_:
                return this.visitLet_(ctx.let_());
            case CPnextParser.RULE_letRec:
                return this.visitLetRec(ctx.letRec());
            case CPnextParser.RULE_open_:
                return this.visitOpen_(ctx.open_());
            case CPnextParser.RULE_ifElse:
                return this.visitIfElse(ctx.ifElse());
            case CPnextParser.RULE_trait:
                return this.visitTrait(ctx.trait());
            case CPnextParser.RULE_new_:
                return this.visitNew_(ctx.new_());
            case CPnextParser.RULE_toString_:
                return this.visitToString_(ctx.toString_());
            case CPnextParser.RULE_fold:
                return this.visitFold(ctx.fold());
            case CPnextParser.RULE_unfold:
                return this.visitUnfold(ctx.unfold());
            default:
                console.error("Error in Lexpr");
        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#lambda.
    visitLambda(ctx) {
        return new AST.TmAbs(
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitExpression(ctx.expression())
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#bigLambda.
    visitBigLambda(ctx) {
        return new AST.TmTAbs(
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.visitExpression(ctx.expression())
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#let_.
    visitLet_(ctx) {
        return new AST.TmLet(
            this.visitTermNameDecl(ctx.termNameDecl()),
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#letRec.
    visitLetRec(ctx) {
        return new AST.TmLetrec(
            this.visitTermNameDecl(ctx.termNameDecl()),
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitType(ctx.type()),
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#open_.
    visitOpen_(ctx) {
        return new AST.TmOpen(
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#ifElse.
    visitIfElse(ctx) {
        return new AST.TmIf(
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1)),
            this.visitExpression(ctx.expression(2))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#trait.
    visitTrait(ctx) {
        let x = new AST.TmTrait(
            ctx.selfAnno() === null ? P.Nothing.value : new P.Just(this.visitSelfAnno(ctx.selfAnno())),
            ctx.type() === null ? P.Nothing.value : new P.Just(this.visitType(ctx.type())),
            ctx.opexpr().length === 2 ? new P.Just(this.visitOpexpr(ctx.opexpr(0))) : P.Nothing.value,
            ctx.opexpr().length === 2 ? this.visitOpexpr(ctx.opexpr(1)) : this.visitOpexpr(ctx.opexpr(0))
        );
        console.log(x);
        return x;
    }
  
  
    // Visit a parse tree produced by CPnextParser#new_.
    visitNew_(ctx) {
        return new AST.TmNew(
            this.visitOpexpr(ctx.opexpr())
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#toString_.
    visitToString_(ctx) {
        return new AST.TmToString(
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by CPnextParser#fold.
	visitFold(ctx) {
        return new AST.TmFold(
            this.visitAtype(ctx.atype()),
            this.visitDotexpr(ctx.dotexpr())
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#unfold.
    visitUnfold(ctx) {
        return new AST.TmUnfold(
            this.visitAtype(ctx.atype()),
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by CPnextParser#fexpr.
    visitFexpr(ctx) {
        const c = ctx.getChild(0);
        let fexpr = undefined;
        let isCtor = undefined;
        switch(c.ruleIndex){
            case CPnextParser.RULE_typeNameDecl:
                fexpr = new AST.TmVar(this.visitTypeNameDecl(c));
                isCtor = true;
                break;
            case CPnextParser.RULE_dotexpr:
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
            } else if (child.ruleIndex === CPnextParser.RULE_dotexpr) {
                fexpr = new AST.TmApp(fexpr, this.visitDotexpr(child));
            } else if (child.ruleIndex === CPnextParser.RULE_atype) {
                fexpr = new AST.TmTApp(fexpr, this.visitAtype(child));
            } else {
                console.error("Error at fexpr");
            }
        }
        if (isCtor){
            return new AST.TmNew(fexpr);
        } else {
            return fexpr;
        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#dotexpr.
    visitDotexpr(ctx) {
        let dotexpr = this.visitAexpr(ctx.aexpr());
        for (let i = 0;i<ctx.label().length; i++){
            dotexpr = new AST.TmPrj(dotexpr, this.visitLabel(ctx.label(i)));
        }
        return dotexpr;
    }
  
  
    // Visit a parse tree produced by CPnextParser#aexpr.
    visitAexpr(ctx) {
        let child = ctx.getChild(0);
        if (child.ruleIndex === undefined){
            switch (child.symbol.type){
                case CPnextParser.Number:
                    let num = child.getText();
                    if (num.includes('.') || num.includes('e') || num.includes('E')){
                        return new AST.TmDouble(parseFloat(num));
                    } else if ('Xx'.includes(num[1])){
                        return new AST.TmInt(parseInt(num.slice(2), 16));
                    } else if ('Oo'.includes(num[1])){
                        return new AST.TmInt(parseInt(num.slice(2), 8));
                    } else {
                        return new AST.TmInt(parseInt(num));
                    }
                case CPnextParser.String:
                    let s = child.getText().slice(1,-1);
                    let s_ = "";
                    for (let i=0;i<s.length;i++){
                        if(s[i]=='\\'){
                            i++;
                            let chars = "\'\"\\bfnrtv";
                            let escs  = "\'\"\\\b\f\n\r\t\v";
                            for(let j=0;j<chars.length;j++){
                                if(s[i] === chars[j])
                                    s_ += escs[j]
                            }
                        } else {
                            s_ += s[i]
                        }
                    }
                    return new AST.TmString(s_);
                case CPnextParser.Unit:
                    return AST.TmUnit.value;
                case CPnextParser.True_:
                    return new AST.TmBool(true);
                case CPnextParser.False_:
                    return new AST.TmBool(false);
                case CPnextParser.Undefined_:
                    return AST.TmUndefined.value;
                case CPnextParser.Dollar:
                    return new AST.TmVar(this.visitTypeNameDecl(ctx.typeNameDecl()));
                case CPnextParser.ParenOpen:
                    return this.visitExpression(ctx.expression());
                default:
                    console.error("error at aexpr");
            }
        } else {
            switch (child.ruleIndex){
                case CPnextParser.RULE_termName:
                    return this.visitTermName(ctx.termName());
                case CPnextParser.RULE_document:
                    return this.visitDocument(ctx.document());
                case CPnextParser.RULE_array:
                    return this.visitArray(ctx.array());
                case CPnextParser.RULE_record:
                    return this.visitRecord(ctx.record());
                case CPnextParser.RULE_recordUpdate:
                    return this.visitRecordUpdate(ctx.recordUpdate());
                default:
                    console.error("Error at Aexpr");
            }
        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#array.
    visitArray(ctx) {
        return new AST.TmArray(
            ctx.expression().map(this.visitExpression, this)
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#record.
    visitRecord(ctx) {
        const record = [];
        for(let i = 0; i<ctx.getChildCount(); i++) {
            let child = ctx.getChild(i);
            if(child.ruleIndex === undefined){
                continue;
            } else {
                switch (child.ruleIndex) {
                    case CPnextParser.RULE_recordField:
                        record.push(this.visitRecordField(child));
                        break;
                    case CPnextParser.RULE_methodPattern:
                        record.push(this.visitMethodPattern(child));
                        break;
                    case CPnextParser.RULE_defaultPattern:
                        record.push(this.visitDefaultPattern(child));
                        break;
                    default:
                        console.error("Error in record");
                }
            }
        }
        return new AST.TmRcd(this.listify(record));
    }
  
  
    // Visit a parse tree produced by CPnextParser#recordField.
    visitRecordField(ctx) {
        return new AST.RcdField(
            ctx.Override() !== null,
            this.visitLabelDecl(ctx.labelDecl()),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            new P.Left(this.visitExpression(ctx.expression()))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#recordUpdate.
    visitRecordUpdate(ctx) {
        const fields = [];
        for (let i=0;i<ctx.labelDecl().length;i++){
            fields.push(new P.Tuple(
                this.visitLabelDecl(ctx.labelDecl(i)),
                this.visitExpression(ctx.expression(i+1))
            ));
        }
        return new AST.TmUpdate(
            this.visitExpression(ctx.expression(0)), this.listify(fields)
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#methodPattern.
    visitMethodPattern(ctx) {
        const params = [];
        const params_ = [];
        let j = 0;
        for (let i = 0;i<ctx.getChildCount();i++){
            if(ctx.getChild(i).ruleIndex === CPnextParser.RULE_termParam){
                if (j == 0)
                    params.push(this.visitTermParam(ctx.getChild(i)));
                else
                    params_.push(this.visitTermParam(ctx.getChild(i)));
            } else {
                if (i > 0 && ctx.getChild(i-1).ruleIndex === CPnextParser.RULE_termParam){
                    j++;
                }
            }
        }
        return new AST.RcdField(
            ctx.Override() !== null,
            this.visitLabelDecl(ctx.labelDecl(0)),
            this.listify(params),
            new P.Right(new AST.MethodPattern(
                ctx.selfAnno() === null? P.Nothing.value : new P.Just(this.visitSelfAnno(ctx.selfAnno())),
                this.visitLabelDecl(ctx.labelDecl(1)),
                this.listify(params_),
                this.visitExpression(ctx.expression())
            ))
        );
    }
  

	// Visit a parse tree produced by CPnextParser#defaultPattern.
	visitDefaultPattern(ctx) {
        return new AST.DefaultPattern(
            new AST.MethodPattern(
                ctx.selfAnno() === null? P.Nothing.value : new P.Just(this.visitSelfAnno(ctx.selfAnno())),
                this.visitLabelDecl(ctx.labelDecl()),
                this.listify(ctx.termParam().map(this.visitTermParam, this)),
                this.visitExpression(ctx.expression())
            )
        );
    }

  
    // Visit a parse tree produced by CPnextParser#typeParam.
    visitTypeParam(ctx) {
        return new P.Tuple(
            this.visitTypeNameDecl(ctx.typeNameDecl()),
            ctx.type() === null? P.Nothing.value : new P.Just(this.visitType(ctx.type()))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#termParam.
    visitTermParam(ctx) {
        switch (ctx.getChildCount()){
            case 1:
                switch (ctx.getChild(0).ruleIndex){
                    case CPnextParser.RULE_termId:
                        return new AST.TmParam(
                            this.visitTermId(ctx.termId()),
                            P.Nothing.value
                        );
                    case CPnextParser.RULE_wildcard:
                        return this.visitWildcard(ctx.wildcard());
                    default:
                        console.error("Error at TermParam");
                        break;
                }
            case 5:
                return new AST.TmParam(
                    this.visitTermId(ctx.termId()),
                    new P.Just(this.visitType(ctx.type()))
                );
            default:
                console.error("Error at TermParam");

        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#termId.
    visitTermId(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by CPnextParser#wildcard.
    visitWildcard(ctx) {
        const labelDecls = ctx.labelDecl().map(this.visitLabelDecl, this);
        const expressions = ctx.expression().map(this.visitExpression, this);
        const defaultFields = [];
        for (let i = 0; i<labelDecls.length; i++){
            defaultFields.push(new P.Tuple(labelDecls[i], expressions[i]));
        }
        return new AST.WildCard(this.listify(defaultFields));
    }
  
  
    // Visit a parse tree produced by CPnextParser#selfAnno.
    visitSelfAnno(ctx) {
        return new P.Tuple(
            this.visitTermNameDecl(ctx.termNameDecl()),
            ctx.type() === null ? P.Nothing.value : new P.Just(this.visitType(ctx.type()))
        );
    }
  
  
    // Visit a parse tree produced by CPnextParser#sort.
    visitSort(ctx) {
        if (ctx.TraitArrow() === null){
            const ti = this.visitType(ctx.type(0));
            const to = P.Nothing.value;
            return new AST.TySort(ti, to);
        } else {
            const ti = this.visitType(ctx.type(0));
            const to = new P.Just(this.visitType(ctx.type(1)));
            return new AST.TySort(ti, to);
        };
    }
  
  
    // Visit a parse tree produced by CPnextParser#typeNameDecl.
    visitTypeNameDecl(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by CPnextParser#typeName.
    visitTypeName(ctx) {
        return new AST.TyVar(ctx.getText());
    }
  
  
    // Visit a parse tree produced by CPnextParser#termNameDecl.
    visitTermNameDecl(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by CPnextParser#termName.
    visitTermName(ctx) {
        switch (ctx.getChild(0).symbol.type){
            case CPnextParser.Lowerid:
                return new AST.TmVar(ctx.getText());
            case CPnextParser.Upperid:
                return new AST.TmNew(new AST.TmVar(ctx.getText()));
            default:
                console.error("Error in termName");
        }
    }
  
  
    // Visit a parse tree produced by CPnextParser#labelDecl.
    visitLabelDecl(ctx) {
        return ctx.getText();
    }
  
  
    // Visit a parse tree produced by CPnextParser#label.
    visitLabel(ctx) {
        return ctx.getText();
    }
  

    // Visit a parse tree produced by CPnextParser#document.
	visitDocument(ctx) {
        const position = {line: ctx.start.line, column: ctx.start.column};
        const docs = ctx.docElement();
        let foldedDocs = undefined;
        if (docs.length === 0){
            foldedDocs = new AST.TmNew(new AST.TmApp(
                new AST.TmVar("Str"),
                new AST.TmString("")
            ));
        } else {
            foldedDocs = this.visitDocElement(docs[0]);
            for (let each of docs.slice(1)){
                console.log("Heyy");
                foldedDocs = new AST.TmNew(new AST.TmApp(
                    new AST.TmApp(new AST.TmVar("Comp"), foldedDocs),
                    this.visitDocElement(each)
                ));
            }
        }
        return new AST.TmPos(
            position,
            new AST.TmDoc(
                foldedDocs
            )
        );
	}


	// Visit a parse tree produced by CPnextParser#docElement.
	visitDocElement(ctx) {
        const child = ctx.getChild(0);
        switch (child.ruleIndex){
            case CPnextParser.RULE_command:
                return this.visitCommand(child);
            case CPnextParser.RULE_interpolation:
                return this.visitInterpolation(child);
            case CPnextParser.RULE_newline:
                return this.visitNewline(child);
            case CPnextParser.RULE_plaintext:
                return this.visitPlaintext(child);
            default:
                console.error("Error ar DocElement");
        }
	}


	// Visit a parse tree produced by CPnextParser#command.
	visitCommand(ctx) {
        const position = {line: ctx.start.line, column: ctx.start.column};
	    const cmd = ctx.getChild(0).getText().slice(1);
        const args = ctx.arg().map(this.visitArg, this);
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


	// Visit a parse tree produced by CPnextParser#interpolation.
	visitInterpolation(ctx) {
	    return new AST.TmNew(new AST.TmApp(
            new AST.TmVar("Str"),
            new AST.TmToString(this.visitExpression(ctx.expression()))
        ));
	}


	// Visit a parse tree produced by CPnextParser#newline.
	visitNewline(ctx) {
        return new AST.TmNew(new AST.TmVar("Endl"));
	}


	// Visit a parse tree produced by CPnextParser#plaintext.
	visitPlaintext(ctx) {
        return new AST.TmNew(new AST.TmApp(
            new AST.TmVar("Str"),
            new AST.TmString(ctx.getText())
        ));
	}


	// Visit a parse tree produced by CPnextParser#arg.
	visitArg(ctx) {
	    switch(ctx.getChild(0).symbol.type){
            case CPnextParser.ParenOpenInTag:
                return this.visitExpression(ctx.expression());
            case CPnextParser.BraceOpenInTag:
                return new AST.TmRcd(this.listify(
                    ctx.recordArgField().map(this.visitRecordArgField, this)
                ));
            case CPnextParser.BracketOpenInTag:
                return this.visitDocument(ctx);
            default:
                console.error("Error in Arg");
        };
	}


	// Visit a parse tree produced by CPnextParser#recordArgField.
	visitRecordArgField(ctx) {
	    const params = this.listify(ctx.termParam().map(this.visitTermParam, this));
        return new AST.RcdField(
            false,
            this.visitLabelDecl(ctx.labelDecl()),
            params,
            new P.Left(this.visitExpression(ctx.expression()))
        );
	}

}
