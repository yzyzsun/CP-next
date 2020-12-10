require 'sinatra'

get '/docs' do
  docs = Dir['public/docs/*'].sort.map do |f|
    f = f.split('/').last
    "<li><a href=#{f}>#{f}</a></li>"
  end
  '<ul>' + docs.join + '</ul>'
end

post '/docs/:name' do |name|
  file = 'public/docs/' + name
  if File.exist? file
    403
  else
    File.write file, request.body.read
    200
  end
end

get /\/(\w*)/ do |name|
  File.read 'public/index.html'
end
