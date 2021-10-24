import antlr4 from 'antlr4';
import ZordLexer from './ZordLexer.js';
import ZordParser from './ZordParser.js';
import ZordASTMaker from './ZordASTMaker.js';
import * as AST from './ASTConstructors.cjs';

export function parse(input) {
  const chars = new antlr4.InputStream(input);
  const lexer = new ZordLexer(chars);
  const tokens = new antlr4.CommonTokenStream(lexer);
  const parser = new ZordParser(tokens);
  parser.buildParseTrees = true;
  const tree = parser.program();
  const ASTMaker = new ZordASTMaker();
  let ast = tree.accept(ASTMaker);
  return ast;
}
