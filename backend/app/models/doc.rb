class Doc < ApplicationRecord
  enum mode: [:program, :module, :doc_only]
  enum access: [:priv, :pub, :open]
  belongs_to :user, optional: true
  validates :name, uniqueness: true
  validates :code, :mode, :access, presence: true
end
