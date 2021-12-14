import antlr4 from 'antlr4';
import CPnextLexer from './CPnextLexer.js';
import CPnextParser from './CPnextParser.js';
import CPnextASTMaker from './CPnextASTMaker.js';

export function parse(input) {
  const chars = new antlr4.InputStream(input);
  const lexer = new CPnextLexer(chars);
  const tokens = new antlr4.CommonTokenStream(lexer);
  const parser = new CPnextParser(tokens);
  parser.buildParseTrees = true;
  const tree = parser.program();
  const ASTMaker = new CPnextASTMaker();
  let ast = tree.accept(ASTMaker);
  return ast;
}
