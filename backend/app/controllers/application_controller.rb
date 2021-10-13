class ApplicationController < ActionController::Base
  private
    def after_sign_in_path_for(resource)
      if request.referer.end_with? new_user_session_path
        "/#{resource.username}"
      else
        request.referer
      end
    end
    def after_sign_out_path_for(resource_or_scope)
      request.referer
    end
end
