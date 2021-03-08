class Doc < ApplicationRecord
  enum mode: [:program, :module, :doc_only]
  enum access: [:priv, :pub, :open]
  belongs_to :user
  validates :name, uniqueness: { scope: :user }
  validates :code, :mode, :access, presence: true

  def path
    "/#{user.username}/#{name}"
  end
end
