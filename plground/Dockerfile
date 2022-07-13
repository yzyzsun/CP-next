FROM timbru31/ruby-node
WORKDIR /plground
COPY . .
RUN bundle install \
 && bin/rails db:setup
CMD bin/rails server -b 0.0.0.0 -p 3000
