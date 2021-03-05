class ApplicationController < ActionController::Base
  def after_sign_in_path_for(user)
    "/#{user.username}"
  end
end
