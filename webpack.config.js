const path = require('path');
const MinimizerPlugin = require('minimizer-webpack-plugin');

module.exports = {
  mode: 'production',
  entry: './app.js',
  module: {
    rules: [
      {
        test: /\.grammar$/,
        use: "lezer-loader",
      },
    ],
  },
  resolve: {
    fallback: {
      fs: false,
    },
  },
  optimization: {
    minimizer: [new MinimizerPlugin({
      extractComments: false,
    })],
  },
  performance: { hints: false },
  output: {
    filename: 'bundle.js',
    path: path.resolve(__dirname, 'plground/app/assets/javascripts'),
    library: 'bundle',
  },
};
