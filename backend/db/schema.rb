# This file is auto-generated from the current state of the database. Instead
# of editing this file, please use the migrations feature of Active Record to
# incrementally modify your database, and then regenerate this schema definition.
#
# This file is the source Rails uses to define your schema when running `bin/rails
# db:schema:load`. When creating a new database, `bin/rails db:schema:load` tends to
# be faster and is potentially less error prone than running all of your
# migrations from scratch. Old migrations may fail to apply correctly if those
# migrations use external dependencies or application code.
#
# It's strongly recommended that you check this file into your version control system.

ActiveRecord::Schema.define(version: 2021_04_26_063413) do

  create_table "docs", force: :cascade do |t|
    t.string "name"
    t.integer "mode", null: false
    t.string "provide_factory"
    t.string "require_library"
    t.datetime "created_at", precision: 6, null: false
    t.datetime "updated_at", precision: 6, null: false
    t.integer "access", null: false
    t.integer "user_id"
    t.text "html_cache"
    t.index ["user_id", "name"], name: "index_docs_on_user_id_and_name", unique: true
    t.index ["user_id"], name: "index_docs_on_user_id"
  end

  create_table "users", force: :cascade do |t|
    t.string "encrypted_password", default: "", null: false
    t.datetime "remember_created_at"
    t.datetime "created_at", precision: 6, null: false
    t.datetime "updated_at", precision: 6, null: false
    t.string "username", default: "", null: false
    t.index ["username"], name: "index_users_on_username", unique: true
  end

  add_foreign_key "docs", "users"
end
