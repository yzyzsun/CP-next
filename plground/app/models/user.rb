class User < ApplicationRecord
  # Include default devise modules. Others available are:
  # :validatable, :recoverable, :confirmable, :lockable,
  # :timeoutable, :trackable and :omniauthable
  devise :database_authenticatable, :registerable, :rememberable
  has_many :docs
  validates :username, uniqueness: { case_sensitive: false },
                       format: { with: /\A\w+\z/ }
  validates :password, presence: true, confirmation: true,
                       length: { in: Devise.password_length }
  validates :password_confirmation, presence: true
end
