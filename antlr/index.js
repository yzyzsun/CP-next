import antlr4 from 'antlr4';
import CPLexer from './CPLexer.js';
import CPParser from './CPParser.js';
import CPVisitor from './CPVisitor.js';

class CPLexerUpdated extends CPLexer {
  constructor(input){
    super(input);
  }

  popMode() {
    if (this._modeStack.length === 0) {
      if (this._interp.debug) {
        console.log("Mode Stack Empty. Mode remains unchanged");
      }
      return this._mode;
    }
    if (this._interp.debug) {
      console.log("popMode back to " + this._modeStack.slice(0, -1));
    }
    this.mode(this._modeStack.pop());
    return this._mode;
  }
} 

class CPErrorListener extends antlr4.error.ErrorListener {
  constructor() {
      super();
  }

  syntaxError(recognizer, offendingSymbol, line, column, msg, e) {
      throw ("SyntaxError at line " + line + ":" + column + "\n" + msg.charAt(0).toUpperCase() + msg.slice(1));
  }
}

export function parse(input) {
  const chars = new antlr4.InputStream(input);
  const lexer = new CPLexerUpdated(chars);
  lexer.removeErrorListeners();
  lexer.addErrorListener(new CPErrorListener);
  const tokens = new antlr4.CommonTokenStream(lexer);
  const parser = new CPParser(tokens);
  parser.buildParseTrees = true;
  parser.removeErrorListeners();
  parser.addErrorListener(new CPErrorListener);
  const tree = parser.program();
  return tree.accept(new CPVisitor);
}
