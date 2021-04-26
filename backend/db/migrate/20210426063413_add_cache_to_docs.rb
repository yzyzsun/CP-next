class AddCacheToDocs < ActiveRecord::Migration[6.1]
  def change
    add_column :docs, :html_cache, :text
  end
end
