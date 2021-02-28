const path = require('path');

const isWebpackDevServer = process.argv.some(a => path.basename(a) === 'webpack-dev-server');
const isWatch = process.argv.some(a => a === '--watch');

module.exports = {
  entry: './app.js',
  module: {
    rules: [
      {
        test: /\.purs$/,
        exclude: /node_modules/,
        use: [
          {
            loader: 'purs-loader',
            options: {
              spago: true,
              pscIde: true,
              watch: isWebpackDevServer || isWatch,
            },
          },
        ],
      },
    ],
  },
  performance: { hints: false },
  output: {
    filename: 'bundle.js',
    path: path.resolve(__dirname, 'backend/app/assets/javascripts'),
    library: 'bundle',
  },
};
