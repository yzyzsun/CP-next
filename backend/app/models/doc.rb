class Doc < ApplicationRecord
  enum mode: [:program, :library, :doc_only]
  enum access: [:priv, :pub, :open]
  belongs_to :user
  validates :name, uniqueness: { scope: :user }
  validates :mode, :access, presence: true

  def path
    "/#{user.username}/#{name}"
  end

  def file
    ext = {
      "program"  => ".zord",
      "library"  => ".mzord",
      "doc_only" => ".zordoc",
    }
    File.join Rails.root, "docs", user.username, name + ext[mode]
  end

  def code
    File.read file
  rescue
    ""
  end
end
