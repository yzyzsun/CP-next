class DocsController < ApplicationController
  before_action :set_doc, only: [:show, :update]

  def create
    if user_signed_in?
      doc = current_user.docs.build(doc_params)
      if doc.save
        File.write doc.file, params[:code]
        render plain: doc.path
      else
        head :unprocessable_entity
      end
    else
      redirect_to :root, alert: "You cannot create a document unless logged in!"
    end
  end

  def destroy
    doc = Doc.find_by(user: current_user, name: params[:id])
    if doc
      if doc.destroy
        File.delete doc.file
        redirect_to :root
      else
        :unprocessable_entity
      end
    else
      head :not_found
    end
  end

  def show
    if @doc.priv? && @doc.user != current_user
      head :unauthorized
    else
      respond_to do |format|
        format.text { render plain: @doc.code }
        format.json { render json: @doc, methods: :code }
      end
    end
  end

  def update
    if @doc.open? || @doc.user == current_user
      old_file = @doc.file
      if @doc.update(doc_params)
        File.delete old_file
        File.write @doc.file, params[:code]
        head :ok
      else
        head :unprocessable_entity
      end
    else
      head :unauthorized
    end
  end

  private
    def set_doc
      @user = User.find_by(username: params[:user])
      @doc = Doc.find_by(user: @user, name: params[:name])
      head :not_found unless @doc
    end

    def doc_params
      params.permit(:name, :access, :mode, :provide_factory, :require_library)
    end
end
