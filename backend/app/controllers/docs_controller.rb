class DocsController < ApplicationController
  before_action :set_doc, only: [:show, :update, :destroy]

  def index
    @docs = Doc.where(access: [:pub, :open])
  end

  def create
    if user_signed_in?
      doc = current_user.docs.build(doc_params)
    else
      doc = Doc.new(doc_params)
    end
    if doc.save
      head :ok
    else
      head :unprocessable_entity
    end
  end

  def show
    if @doc.priv? && @doc.user != current_user
      head :not_found
    end
  end

  def update
    if @doc.open? || @doc.user == current_user
      if @doc.update(doc_params)
      else
      end
    else
    end
  end

  def destory
    if @doc.user == current_user
    else
    end
  end

  private
    def set_doc
      @doc = Doc.find_by(name: params[:id])
      head :not_found unless @doc
    end

    def doc_params
      params.permit(:name, :code, :access, :mode, :provide_factory, :require_module)
    end
end
