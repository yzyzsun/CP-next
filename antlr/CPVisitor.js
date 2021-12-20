import CPParser from './CPParser.js';
import CPParserVisitor from './CPParserVisitor.js';

import { default as AST } from '../src/CP/Syntax/Source.purs';
import { default as OP } from '../src/CP/Syntax/Common.purs';
import { default as PS } from '../src/PS.purs';


export default class CPVisitor extends CPParserVisitor {

    // Convert array to list
    listify(array) {
        let list = PS.Nil.value;
        for (let each of array.reverse()){
            list = new PS.Cons(each, list);
        }
        return list;
    }


    // Visit a parse tree produced by CPParser#program.
	visitProgram(ctx) {
        const expression = ctx.expression();
        const definitions = ctx.definition();
        let program = this.visitExpression(expression);
        for(let i = definitions.length - 1; i>=0; i--){
            program = this.visitDefinition(definitions[i], program);
        }
        return program;
    }


    // Visit a parse tree produced by CPParser#open.
    visitOpen(ctx) {
        return null;
    }


    // Visit a parse tree produced by CPParser#definition.
    visitDefinition(ctx, program) {
        const typeDef = ctx.typeDef();
        const termDef = ctx.termDef();
        if (typeDef !== null)
            return this.visitTypeDef(typeDef, program);
        else
            return this.visitTermDef(termDef, program);
    }


    // Visit a parse tree produced by CPParser#typeDef.
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


    // Visit a parse tree produced by CPParser#termDef.
    visitTermDef(ctx, p) {
        const x = this.visitTermNameDecl(ctx.termNameDecl());
        const tys = this.listify(ctx.typeParam().map(this.visitTypeParam, this));
        const tms = this.listify(ctx.termParam().map(this.visitTermParam, this));
        const t = ctx.type() === null ? PS.Nothing.value : new PS.Just(this.visitType(ctx.type()));
        const e = this.visitExpression(ctx.expression());
        return new AST.TmDef(x, tys, tms, t, e, p);
    }


    // Visit a parse tree produced by CPParser#type.
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


    // Visit a parse tree produced by CPParser#btype.
    visitBtype(ctx) {
        if (ctx.ForAll() !== null) {
            return new AST.TyForall(this.listify(ctx.typeParam().map(this.visitTypeParam, this)), this.visitType(ctx.type(0)));
        } else if (ctx.TraitCaps() !== null){
            if (ctx.TraitArrow() === null){
                const ti = PS.Nothing.value;
                const to = this.visitType(ctx.type(0));
                return new AST.TyTrait(ti, to);
            } else {
                const ti = new PS.Just(this.visitType(ctx.type(0)));
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
                } else if (child.ruleIndex === CPParser.RULE_sort){
                    btype = new AST.TyApp(btype, this.visitSort(child));
                } else if (child.ruleIndex === CPParser.RULE_atype){
                    btype = new AST.TyApp(btype, this.visitAtype(child));
                } else {
                    console.error("Error at btype");
                }
            }
            return btype;
        }
    }


    // Visit a parse tree produced by CPParser#atype.
	visitAtype(ctx) {
        if (ctx.getChild(0).symbol === undefined){
            switch (ctx.getChild(0).ruleIndex) {
                case CPParser.RULE_typeName:
                    return this.visitTypeName(ctx.typeName());
                case CPParser.RULE_recordType:
                    return this.visitRecordType(ctx.recordType());
                default:
                    console.error("Error at atype");
            }
        } else {
            switch (ctx.getChild(0).symbol.type) {
                case CPParser.Int :
                    return AST.TyInt.value;
                case CPParser.Double :
                    return AST.TyDouble.value;
                case CPParser.Bool :
                    return AST.TyBool.value;
                case CPParser.StringType :
                    return AST.TyString.value;
                case CPParser.Top :
                    return AST.TyTop.value;
                case CPParser.Bot :
                    return AST.TyBot.value;
                case CPParser.BracketOpen :
                    return new AST.TyArray(
                        this.visitType(ctx.type())
                    );
                case CPParser.ParenOpen :
                    return this.visitType(ctx.type());
                default:
                    console.error("Error at atype");
            }
        }
    }


    // Visit a parse tree produced by CPParser#recordType.
    visitRecordType(ctx) {
        return new AST.TyRcd(this.listify(ctx.recordTypeElement().map(this.visitRecordTypeElement, this)));
    }

    // Visit a parse tree produced by CPParser#recordTypeElement.
	visitRecordTypeElement(ctx) {
        return new AST.RcdTy(
            this.visitLabelDecl(ctx.labelDecl()),
            this.visitType(ctx.type()),
            ctx.Question() !== null
        );
    }


    // Visit a parse tree produced by CPParser#expression.
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

    // Visit a parse tree produced by CPParser#opexpr.
	visitOpexpr(ctx) {
        const count = ctx.getChildCount();
        let op = null
        switch (count) {
            case 1:
                return this.visitLexpr(ctx.lexpr());
            case 2:
                const opexpr = this.visitOpexpr(ctx.opexpr(0));
                switch (ctx.getChild(0).symbol.type) {
                    case CPParser.Minus:
                        op = OP.Neg.value;
                        break;
                    case CPParser.Not:
                        op = OP.Not.value;
                        break;
                    case CPParser.Length:
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
                    case CPParser.Index:
                        op = OP.Index.value;
                        break;
                    case CPParser.Modulo:
                        op = new OP.Arith(OP.Mod.value);
                        break;
                    case CPParser.Divide:
                        op = new OP.Arith(OP.Div.value);
                        break;
                    case CPParser.Star:
                        op = new OP.Arith(OP.Mul.value);
                        break;
                    case CPParser.Minus:
                        op = new OP.Arith(OP.Sub.value);
                        break;
                    case CPParser.Plus:
                        op = new OP.Arith(OP.Add.value);
                        break;
                    case CPParser.Append:
                        op = OP.Append.value;
                        break;
                    case CPParser.Less:
                        op = new OP.Comp(OP.Lt.value);
                        break;
                    case CPParser.Greater:
                        op = new OP.Comp(OP.Gt.value);
                        break;
                    case CPParser.LessEqual:
                        op = new OP.Comp(OP.Le.value);
                        break;
                    case CPParser.GreaterEqual:
                        op = new OP.Comp(OP.Ge.value);
                        break;
                    case CPParser.Equal:
                        op = new OP.Comp(OP.Eql.value);
                        break;
                    case CPParser.NotEqual:
                        op = new OP.Comp(OP.Neq.value);
                        break;
                    case CPParser.And:
                        op = new OP.Logic(OP.And.value);
                        break;
                    case CPParser.Or:
                        op = new OP.Logic(OP.Or.value);
                        break;
                    case CPParser.Forward:
                        return new AST.TmForward(opexpr1, opexpr2);
                    case CPParser.Merge:
                        return new AST.TmMerge(opexpr1, opexpr2);
                    default:
                        console.error("Error in Binary Opexpr");
                }
                return new AST.TmBinary(op, opexpr1, opexpr2);
        }

    }

	// Visit a parse tree produced by CPParser#lexpr.
	visitLexpr(ctx) {
        switch (ctx.getChild(0).ruleIndex) {
            case CPParser.RULE_fexpr:
                return this.visitFexpr(ctx.fexpr());
            case CPParser.RULE_lambda:
                return this.visitLambda(ctx.lambda());
            case CPParser.RULE_bigLambda:
                return this.visitBigLambda(ctx.bigLambda());
            case CPParser.RULE_let_:
                return this.visitLet_(ctx.let_());
            case CPParser.RULE_letRec:
                return this.visitLetRec(ctx.letRec());
            case CPParser.RULE_open_:
                return this.visitOpen_(ctx.open_());
            case CPParser.RULE_ifElse:
                return this.visitIfElse(ctx.ifElse());
            case CPParser.RULE_trait:
                return this.visitTrait(ctx.trait());
            case CPParser.RULE_new_:
                return this.visitNew_(ctx.new_());
            case CPParser.RULE_toString_:
                return this.visitToString_(ctx.toString_());
            case CPParser.RULE_fold:
                return this.visitFold(ctx.fold());
            case CPParser.RULE_unfold:
                return this.visitUnfold(ctx.unfold());
            default:
                console.error("Error in Lexpr");
        }
    }


    // Visit a parse tree produced by CPParser#lambda.
    visitLambda(ctx) {
        return new AST.TmAbs(
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitExpression(ctx.expression())
        );
    }


    // Visit a parse tree produced by CPParser#bigLambda.
    visitBigLambda(ctx) {
        return new AST.TmTAbs(
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.visitExpression(ctx.expression())
        );
    }


    // Visit a parse tree produced by CPParser#let_.
    visitLet_(ctx) {
        return new AST.TmLet(
            this.visitTermNameDecl(ctx.termNameDecl()),
            this.listify(ctx.typeParam().map(this.visitTypeParam, this)),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }


    // Visit a parse tree produced by CPParser#letRec.
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


    // Visit a parse tree produced by CPParser#open_.
    visitOpen_(ctx) {
        return new AST.TmOpen(
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1))
        );
    }


    // Visit a parse tree produced by CPParser#ifElse.
    visitIfElse(ctx) {
        return new AST.TmIf(
            this.visitExpression(ctx.expression(0)),
            this.visitExpression(ctx.expression(1)),
            this.visitExpression(ctx.expression(2))
        );
    }


    // Visit a parse tree produced by CPParser#trait.
    visitTrait(ctx) {
        let x = new AST.TmTrait(
            ctx.selfAnno() === null ? PS.Nothing.value : new PS.Just(this.visitSelfAnno(ctx.selfAnno())),
            ctx.type() === null ? PS.Nothing.value : new PS.Just(this.visitType(ctx.type())),
            ctx.opexpr().length === 2 ? new PS.Just(this.visitOpexpr(ctx.opexpr(0))) : PS.Nothing.value,
            ctx.opexpr().length === 2 ? this.visitOpexpr(ctx.opexpr(1)) : this.visitOpexpr(ctx.opexpr(0))
        );
        return x;
    }


    // Visit a parse tree produced by CPParser#new_.
    visitNew_(ctx) {
        return new AST.TmNew(
            this.visitOpexpr(ctx.opexpr())
        );
    }


    // Visit a parse tree produced by CPParser#toString_.
    visitToString_(ctx) {
        return new AST.TmToString(
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by CPParser#fold.
	visitFold(ctx) {
        return new AST.TmFold(
            this.visitAtype(ctx.atype()),
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by CPParser#unfold.
    visitUnfold(ctx) {
        return new AST.TmUnfold(
            this.visitAtype(ctx.atype()),
            this.visitDotexpr(ctx.dotexpr())
        );
    }


    // Visit a parse tree produced by CPParser#fexpr.
    visitFexpr(ctx) {
        const c = ctx.getChild(0);
        let fexpr = undefined;
        let isCtor = undefined;
        switch(c.ruleIndex){
            case CPParser.RULE_typeNameDecl:
                fexpr = new AST.TmVar(this.visitTypeNameDecl(c));
                isCtor = true;
                break;
            case CPParser.RULE_dotexpr:
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
            } else if (child.ruleIndex === CPParser.RULE_dotexpr) {
                fexpr = new AST.TmApp(fexpr, this.visitDotexpr(child));
            } else if (child.ruleIndex === CPParser.RULE_atype) {
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


    // Visit a parse tree produced by CPParser#dotexpr.
    visitDotexpr(ctx) {
        let dotexpr = this.visitAexpr(ctx.aexpr());
        for (let i = 0;i<ctx.label().length; i++){
            dotexpr = new AST.TmPrj(dotexpr, this.visitLabel(ctx.label(i)));
        }
        return dotexpr;
    }


    // Visit a parse tree produced by CPParser#aexpr.
    visitAexpr(ctx) {
        let child = ctx.getChild(0);
        if (child.ruleIndex === undefined){
            switch (child.symbol.type){
                case CPParser.Number:
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
                case CPParser.String:
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
                case CPParser.Unit:
                    return AST.TmUnit.value;
                case CPParser.True_:
                    return new AST.TmBool(true);
                case CPParser.False_:
                    return new AST.TmBool(false);
                case CPParser.Undefined_:
                    return AST.TmUndefined.value;
                case CPParser.Dollar:
                    return new AST.TmVar(this.visitTypeNameDecl(ctx.typeNameDecl()));
                case CPParser.ParenOpen:
                    return this.visitExpression(ctx.expression());
                default:
                    console.error("error at aexpr");
            }
        } else {
            switch (child.ruleIndex){
                case CPParser.RULE_termName:
                    return this.visitTermName(ctx.termName());
                case CPParser.RULE_document:
                    return this.visitDocument(ctx.document());
                case CPParser.RULE_array:
                    return this.visitArray(ctx.array());
                case CPParser.RULE_record:
                    return this.visitRecord(ctx.record());
                case CPParser.RULE_recordUpdate:
                    return this.visitRecordUpdate(ctx.recordUpdate());
                default:
                    console.error("Error at Aexpr");
            }
        }
    }


    // Visit a parse tree produced by CPParser#array.
    visitArray(ctx) {
        return new AST.TmArray(
            ctx.expression().map(this.visitExpression, this)
        );
    }


    // Visit a parse tree produced by CPParser#record.
    visitRecord(ctx) {
        const record = [];
        for(let i = 0; i<ctx.getChildCount(); i++) {
            let child = ctx.getChild(i);
            if(child.ruleIndex === undefined){
                continue;
            } else {
                switch (child.ruleIndex) {
                    case CPParser.RULE_recordField:
                        record.push(this.visitRecordField(child));
                        break;
                    case CPParser.RULE_methodPattern:
                        record.push(this.visitMethodPattern(child));
                        break;
                    case CPParser.RULE_defaultPattern:
                        record.push(this.visitDefaultPattern(child));
                        break;
                    default:
                        console.error("Error in record");
                }
            }
        }
        return new AST.TmRcd(this.listify(record));
    }


    // Visit a parse tree produced by CPParser#recordField.
    visitRecordField(ctx) {
        return new AST.RcdField(
            ctx.Override() !== null,
            this.visitLabelDecl(ctx.labelDecl()),
            this.listify(ctx.termParam().map(this.visitTermParam, this)),
            new PS.Left(this.visitExpression(ctx.expression()))
        );
    }


    // Visit a parse tree produced by CPParser#recordUpdate.
    visitRecordUpdate(ctx) {
        const fields = [];
        for (let i=0;i<ctx.labelDecl().length;i++){
            fields.push(new PS.Tuple(
                this.visitLabelDecl(ctx.labelDecl(i)),
                this.visitExpression(ctx.expression(i+1))
            ));
        }
        return new AST.TmUpdate(
            this.visitExpression(ctx.expression(0)), this.listify(fields)
        );
    }


    // Visit a parse tree produced by CPParser#methodPattern.
    visitMethodPattern(ctx) {
        const params = [];
        const params_ = [];
        let j = 0;
        for (let i = 0;i<ctx.getChildCount();i++){
            if(ctx.getChild(i).ruleIndex === CPParser.RULE_termParam){
                if (j == 0)
                    params.push(this.visitTermParam(ctx.getChild(i)));
                else
                    params_.push(this.visitTermParam(ctx.getChild(i)));
            } else {
                if (i > 0 && ctx.getChild(i-1).ruleIndex === CPParser.RULE_termParam){
                    j++;
                }
            }
        }
        return new AST.RcdField(
            ctx.Override() !== null,
            this.visitLabelDecl(ctx.labelDecl(0)),
            this.listify(params),
            new PS.Right(new AST.MethodPattern(
                ctx.selfAnno() === null? PS.Nothing.value : new PS.Just(this.visitSelfAnno(ctx.selfAnno())),
                this.visitLabelDecl(ctx.labelDecl(1)),
                this.listify(params_),
                this.visitExpression(ctx.expression())
            ))
        );
    }


	// Visit a parse tree produced by CPParser#defaultPattern.
	visitDefaultPattern(ctx) {
        return new AST.DefaultPattern(
            new AST.MethodPattern(
                ctx.selfAnno() === null? PS.Nothing.value : new PS.Just(this.visitSelfAnno(ctx.selfAnno())),
                this.visitLabelDecl(ctx.labelDecl()),
                this.listify(ctx.termParam().map(this.visitTermParam, this)),
                this.visitExpression(ctx.expression())
            )
        );
    }


    // Visit a parse tree produced by CPParser#typeParam.
    visitTypeParam(ctx) {
        return new PS.Tuple(
            this.visitTypeNameDecl(ctx.typeNameDecl()),
            ctx.type() === null? PS.Nothing.value : new PS.Just(this.visitType(ctx.type()))
        );
    }


    // Visit a parse tree produced by CPParser#termParam.
    visitTermParam(ctx) {
        switch (ctx.getChildCount()){
            case 1:
                switch (ctx.getChild(0).ruleIndex){
                    case CPParser.RULE_termId:
                        return new AST.TmParam(
                            this.visitTermId(ctx.termId()),
                            PS.Nothing.value
                        );
                    case CPParser.RULE_wildcard:
                        return this.visitWildcard(ctx.wildcard());
                    default:
                        console.error("Error at TermParam");
                        break;
                }
            case 5:
                return new AST.TmParam(
                    this.visitTermId(ctx.termId()),
                    new PS.Just(this.visitType(ctx.type()))
                );
            default:
                console.error("Error at TermParam");

        }
    }


    // Visit a parse tree produced by CPParser#termId.
    visitTermId(ctx) {
        return ctx.getText();
    }


    // Visit a parse tree produced by CPParser#wildcard.
    visitWildcard(ctx) {
        const labelDecls = ctx.labelDecl().map(this.visitLabelDecl, this);
        const expressions = ctx.expression().map(this.visitExpression, this);
        const defaultFields = [];
        for (let i = 0; i<labelDecls.length; i++){
            defaultFields.push(new PS.Tuple(labelDecls[i], expressions[i]));
        }
        return new AST.WildCard(this.listify(defaultFields));
    }


    // Visit a parse tree produced by CPParser#selfAnno.
    visitSelfAnno(ctx) {
        return new PS.Tuple(
            this.visitTermNameDecl(ctx.termNameDecl()),
            ctx.type() === null ? PS.Nothing.value : new PS.Just(this.visitType(ctx.type()))
        );
    }


    // Visit a parse tree produced by CPParser#sort.
    visitSort(ctx) {
        if (ctx.TraitArrow() === null){
            const ti = this.visitType(ctx.type(0));
            const to = PS.Nothing.value;
            return new AST.TySort(ti, to);
        } else {
            const ti = this.visitType(ctx.type(0));
            const to = new PS.Just(this.visitType(ctx.type(1)));
            return new AST.TySort(ti, to);
        };
    }


    // Visit a parse tree produced by CPParser#typeNameDecl.
    visitTypeNameDecl(ctx) {
        return ctx.getText();
    }


    // Visit a parse tree produced by CPParser#typeName.
    visitTypeName(ctx) {
        return new AST.TyVar(ctx.getText());
    }


    // Visit a parse tree produced by CPParser#termNameDecl.
    visitTermNameDecl(ctx) {
        return ctx.getText();
    }


    // Visit a parse tree produced by CPParser#termName.
    visitTermName(ctx) {
        switch (ctx.getChild(0).symbol.type){
            case CPParser.Lowerid:
                return new AST.TmVar(ctx.getText());
            case CPParser.Upperid:
                return new AST.TmNew(new AST.TmVar(ctx.getText()));
            default:
                console.error("Error in termName");
        }
    }


    // Visit a parse tree produced by CPParser#labelDecl.
    visitLabelDecl(ctx) {
        return ctx.getText();
    }


    // Visit a parse tree produced by CPParser#label.
    visitLabel(ctx) {
        return ctx.getText();
    }


    // Visit a parse tree produced by CPParser#document.
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


	// Visit a parse tree produced by CPParser#docElement.
	visitDocElement(ctx) {
        const child = ctx.getChild(0);
        switch (child.ruleIndex){
            case CPParser.RULE_command:
                return this.visitCommand(child);
            case CPParser.RULE_interpolation:
                return this.visitInterpolation(child);
            case CPParser.RULE_newline:
                return this.visitNewline(child);
            case CPParser.RULE_plaintext:
                return this.visitPlaintext(child);
            default:
                console.error("Error ar DocElement");
        }
	}


	// Visit a parse tree produced by CPParser#command.
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


	// Visit a parse tree produced by CPParser#interpolation.
	visitInterpolation(ctx) {
	    return new AST.TmNew(new AST.TmApp(
            new AST.TmVar("Str"),
            new AST.TmToString(this.visitExpression(ctx.expression()))
        ));
	}


	// Visit a parse tree produced by CPParser#newline.
	visitNewline(ctx) {
        return new AST.TmNew(new AST.TmVar("Endl"));
	}


	// Visit a parse tree produced by CPParser#plaintext.
	visitPlaintext(ctx) {
        return new AST.TmNew(new AST.TmApp(
            new AST.TmVar("Str"),
            new AST.TmString(ctx.getText())
        ));
	}


	// Visit a parse tree produced by CPParser#arg.
	visitArg(ctx) {
	    switch(ctx.getChild(0).symbol.type){
            case CPParser.ParenOpenInTag:
                return this.visitExpression(ctx.expression());
            case CPParser.BraceOpenInTag:
                return new AST.TmRcd(this.listify(
                    ctx.recordArgField().map(this.visitRecordArgField, this)
                ));
            case CPParser.BracketOpenInTag:
                return this.visitDocument(ctx);
            default:
                console.error("Error in Arg");
        };
	}


	// Visit a parse tree produced by CPParser#recordArgField.
	visitRecordArgField(ctx) {
	    const params = this.listify(ctx.termParam().map(this.visitTermParam, this));
        return new AST.RcdField(
            false,
            this.visitLabelDecl(ctx.labelDecl()),
            params,
            new PS.Left(this.visitExpression(ctx.expression()))
        );
	}

}
