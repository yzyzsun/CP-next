class RegistrationsController < Devise::RegistrationsController
  protected
    def sign_up(resource_name, resource)
      Dir.mkdir File.join(Rails.root, "docs", resource.username)
      sign_in(resource_name, resource)
    end
end
