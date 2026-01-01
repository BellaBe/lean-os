# Liquid Objects Reference

## Product Object

```liquid
{{ product.id }}                      # Numeric ID
{{ product.title }}                   # Product title
{{ product.handle }}                  # URL-safe handle
{{ product.description }}             # Full description
{{ product.content }}                 # Alias for description
{{ product.type }}                    # Product type
{{ product.vendor }}                  # Vendor name
{{ product.url }}                     # Product URL
{{ product.price }}                   # Current price (cents)
{{ product.price_min }}               # Minimum variant price
{{ product.price_max }}               # Maximum variant price
{{ product.price_varies }}            # True if variants have different prices
{{ product.compare_at_price }}        # Compare at price
{{ product.compare_at_price_min }}
{{ product.compare_at_price_max }}
{{ product.available }}               # True if any variant in stock
{{ product.selected_variant }}        # Currently selected variant
{{ product.selected_or_first_available_variant }}
{{ product.tags }}                    # Array of tags
{{ product.options }}                 # Array of option names
{{ product.options_with_values }}     # Options with their values

{# Images #}
{{ product.featured_image }}          # First image
{{ product.images }}                  # Array of images
{{ product.images[0].src }}
{{ product.images[0].alt }}
{{ product.images[0].width }}
{{ product.images[0].height }}
{{ product.images[0] | img_url: '500x500' }}

{# Media (images, video, 3D models) #}
{{ product.media }}
{% for media in product.media %}
  {% case media.media_type %}
    {% when 'image' %}
      {{ media | image_url: width: 500 | image_tag }}
    {% when 'video' %}
      {{ media | video_tag }}
    {% when 'external_video' %}
      {{ media | external_video_tag }}
    {% when 'model' %}
      {{ media | model_viewer_tag }}
  {% endcase %}
{% endfor %}

{# Variants #}
{{ product.variants }}                # Array of variants
{{ product.variants.first }}
{% for variant in product.variants %}
  {{ variant.id }}
  {{ variant.title }}
  {{ variant.price }}
  {{ variant.sku }}
  {{ variant.available }}
  {{ variant.inventory_quantity }}
  {{ variant.option1 }}
  {{ variant.option2 }}
  {{ variant.option3 }}
  {{ variant.image }}
{% endfor %}

{# Metafields #}
{{ product.metafields.custom.care_instructions }}
{{ product.metafields.custom.care_instructions.value }}
```

## Collection Object

```liquid
{{ collection.id }}
{{ collection.title }}
{{ collection.handle }}
{{ collection.description }}
{{ collection.url }}
{{ collection.image }}
{{ collection.products }}             # Paginated products
{{ collection.products_count }}       # Total products
{{ collection.all_products_count }}
{{ collection.all_tags }}             # All tags in collection
{{ collection.all_types }}            # All product types
{{ collection.all_vendors }}          # All vendors

{# Filtering and sorting #}
{{ collection.sort_by }}
{{ collection.sort_options }}
{{ collection.filters }}
{{ collection.default_sort_by }}

{# Pagination #}
{% paginate collection.products by 12 %}
  {% for product in collection.products %}
    {{ product.title }}
  {% endfor %}
  
  {{ paginate.pages }}
  {{ paginate.current_page }}
  {{ paginate.previous.url }}
  {{ paginate.next.url }}
  
  {% for part in paginate.parts %}
    {% if part.is_link %}
      <a href="{{ part.url }}">{{ part.title }}</a>
    {% else %}
      <span>{{ part.title }}</span>
    {% endif %}
  {% endfor %}
{% endpaginate %}
```

## Cart Object

```liquid
{{ cart.item_count }}
{{ cart.total_price | money }}
{{ cart.total_weight }}
{{ cart.original_total_price | money }}
{{ cart.total_discount | money }}
{{ cart.requires_shipping }}
{{ cart.note }}
{{ cart.attributes.gift_message }}

{# Line items #}
{% for item in cart.items %}
  {{ item.id }}                       # Line item ID
  {{ item.product.title }}
  {{ item.variant.title }}
  {{ item.quantity }}
  {{ item.price | money }}            # Unit price
  {{ item.line_price | money }}       # Total for line
  {{ item.original_price | money }}
  {{ item.original_line_price | money }}
  {{ item.total_discount | money }}
  {{ item.sku }}
  {{ item.url }}
  {{ item.image | img_url: '100x100' }}
  {{ item.properties }}               # Custom properties
  
  {# Remove/update URLs #}
  {{ item.url_to_remove }}
  {{ routes.cart_change_url }}
{% endfor %}

{# Discounts #}
{% for discount in cart.discount_applications %}
  {{ discount.title }}
  {{ discount.total_allocated_amount | money }}
  {{ discount.type }}                 # automatic, discount_code, manual, script
{% endfor %}
```

## Customer Object

```liquid
{% if customer %}
  {{ customer.id }}
  {{ customer.email }}
  {{ customer.first_name }}
  {{ customer.last_name }}
  {{ customer.name }}                 # Full name
  {{ customer.phone }}
  
  {{ customer.orders_count }}
  {{ customer.total_spent | money }}
  {{ customer.tags }}
  
  {# Default address #}
  {{ customer.default_address.address1 }}
  {{ customer.default_address.city }}
  {{ customer.default_address.province }}
  {{ customer.default_address.country }}
  {{ customer.default_address.zip }}
  
  {# All addresses #}
  {% for address in customer.addresses %}
    {{ address.id }}
    {{ address.address1 }}
  {% endfor %}
  
  {# Orders #}
  {% for order in customer.orders %}
    {{ order.name }}                  # Order number
    {{ order.created_at | date: '%B %d, %Y' }}
    {{ order.total_price | money }}
    {{ order.fulfillment_status }}
    {{ order.financial_status }}
  {% endfor %}
{% endif %}
```

## Order Object

```liquid
{{ order.id }}
{{ order.name }}                      # e.g., #1001
{{ order.order_number }}              # Numeric only
{{ order.email }}
{{ order.created_at | date: '%B %d, %Y' }}
{{ order.cancelled }}
{{ order.cancelled_at }}
{{ order.cancel_reason }}

{# Prices #}
{{ order.subtotal_price | money }}
{{ order.total_price | money }}
{{ order.total_tax | money }}
{{ order.total_discounts | money }}

{# Status #}
{{ order.fulfillment_status }}        # fulfilled, partial, unfulfilled
{{ order.fulfillment_status_label }}
{{ order.financial_status }}          # paid, pending, refunded
{{ order.financial_status_label }}

{# Line items #}
{% for line_item in order.line_items %}
  {{ line_item.title }}
  {{ line_item.quantity }}
  {{ line_item.price | money }}
  {{ line_item.sku }}
  {{ line_item.fulfillment.tracking_number }}
  {{ line_item.fulfillment.tracking_url }}
{% endfor %}

{# Addresses #}
{{ order.billing_address.name }}
{{ order.billing_address.address1 }}
{{ order.shipping_address.name }}
{{ order.shipping_address.address1 }}

{# Shipping #}
{% for shipping_method in order.shipping_methods %}
  {{ shipping_method.title }}
  {{ shipping_method.price | money }}
{% endfor %}

{# Transactions #}
{% for transaction in order.transactions %}
  {{ transaction.gateway }}
  {{ transaction.amount | money }}
  {{ transaction.status }}
{% endfor %}
```

## Page Object

```liquid
{{ page.id }}
{{ page.title }}
{{ page.handle }}
{{ page.content }}
{{ page.url }}
{{ page.author }}
{{ page.template_suffix }}
```

## Blog and Article Objects

```liquid
{# Blog #}
{{ blog.id }}
{{ blog.title }}
{{ blog.handle }}
{{ blog.url }}
{{ blog.articles }}
{{ blog.articles_count }}
{{ blog.all_tags }}

{# Article #}
{{ article.id }}
{{ article.title }}
{{ article.handle }}
{{ article.url }}
{{ article.content }}
{{ article.excerpt }}
{{ article.excerpt_or_content }}
{{ article.author }}
{{ article.created_at | date: '%B %d, %Y' }}
{{ article.published_at }}
{{ article.image }}
{{ article.tags }}
{{ article.comments }}
{{ article.comments_count }}

{# Comment #}
{% for comment in article.comments %}
  {{ comment.author }}
  {{ comment.email }}
  {{ comment.content }}
  {{ comment.created_at | date: '%B %d, %Y' }}
{% endfor %}
```

## Shop Object

```liquid
{{ shop.name }}
{{ shop.email }}
{{ shop.description }}
{{ shop.domain }}                     # Primary domain
{{ shop.url }}
{{ shop.secure_url }}
{{ shop.permanent_domain }}           # myshop.myshopify.com

{# Currency and money #}
{{ shop.currency }}                   # e.g., USD
{{ shop.money_format }}               # e.g., ${{amount}}
{{ shop.money_with_currency_format }}

{# Locale #}
{{ shop.locale }}
{{ shop.enabled_locales }}

{# Address #}
{{ shop.address.address1 }}
{{ shop.address.city }}
{{ shop.address.province }}
{{ shop.address.country }}
{{ shop.address.zip }}
{{ shop.phone }}

{# Features #}
{{ shop.customer_accounts_enabled }}
{{ shop.customer_accounts_optional }}

{# Policies #}
{{ shop.privacy_policy.body }}
{{ shop.privacy_policy.url }}
{{ shop.refund_policy.body }}
{{ shop.terms_of_service.body }}
{{ shop.shipping_policy.body }}
```

## Form Objects

```liquid
{# Customer login #}
{% form 'customer_login' %}
  {{ form.errors | default_errors }}
  <input type="email" name="customer[email]">
  <input type="password" name="customer[password]">
  <button type="submit">Login</button>
{% endform %}

{# Customer registration #}
{% form 'create_customer' %}
  {{ form.errors | default_errors }}
  <input type="text" name="customer[first_name]">
  <input type="text" name="customer[last_name]">
  <input type="email" name="customer[email]">
  <input type="password" name="customer[password]">
  <button type="submit">Register</button>
{% endform %}

{# Add to cart #}
{% form 'product', product %}
  <select name="id">
    {% for variant in product.variants %}
      <option value="{{ variant.id }}">{{ variant.title }} - {{ variant.price | money }}</option>
    {% endfor %}
  </select>
  <input type="number" name="quantity" value="1" min="1">
  <button type="submit">Add to Cart</button>
{% endform %}

{# Contact form #}
{% form 'contact' %}
  {{ form.errors | default_errors }}
  {% if form.posted_successfully? %}
    <p>Thanks for contacting us!</p>
  {% endif %}
  <input type="text" name="contact[name]">
  <input type="email" name="contact[email]">
  <textarea name="contact[body]"></textarea>
  <button type="submit">Send</button>
{% endform %}

{# Newsletter #}
{% form 'customer' %}
  <input type="email" name="contact[email]" placeholder="Email">
  <button type="submit">Subscribe</button>
{% endform %}

{# Customer address #}
{% form 'customer_address', customer.new_address %}
  <input type="text" name="address[first_name]">
  <input type="text" name="address[last_name]">
  <input type="text" name="address[address1]">
  <input type="text" name="address[city]">
  <select name="address[country]">
    {{ country_option_tags }}
  </select>
  <button type="submit">Add Address</button>
{% endform %}
```

## Global Objects

```liquid
{# Request #}
{{ request.host }}
{{ request.path }}
{{ request.page_type }}               # product, collection, page, etc.
{{ request.design_mode }}             # true in theme editor

{# Template #}
{{ template }}                        # Template filename
{{ template.name }}                   # e.g., product
{{ template.suffix }}                 # e.g., alternate (for product.alternate.json)
{{ template.directory }}              # templates or customers

{# Routes #}
{{ routes.root_url }}                 # /
{{ routes.account_url }}              # /account
{{ routes.account_login_url }}        # /account/login
{{ routes.account_logout_url }}       # /account/logout
{{ routes.account_register_url }}     # /account/register
{{ routes.account_addresses_url }}    # /account/addresses
{{ routes.collections_url }}          # /collections
{{ routes.all_products_collection_url }}
{{ routes.search_url }}               # /search
{{ routes.cart_url }}                 # /cart
{{ routes.cart_add_url }}             # /cart/add
{{ routes.cart_change_url }}          # /cart/change
{{ routes.cart_clear_url }}           # /cart/clear

{# Localization #}
{{ localization.available_countries }}
{{ localization.available_languages }}
{{ localization.country }}
{{ localization.language }}

{# Content #}
{{ content_for_header }}              # REQUIRED in <head>
{{ content_for_layout }}              # REQUIRED in theme.liquid

{# Canonical URL #}
{{ canonical_url }}

{# Page title #}
{{ page_title }}
{{ page_description }}

{# Scripts #}
{{ scripts }}                         # Shopify Scripts output

{# Predictive search #}
{{ predictive_search.resources }}
```

## Section Object

```liquid
{# Inside a section #}
{{ section.id }}                      # Unique section ID
{{ section.settings.heading }}        # Access settings
{{ section.blocks }}                  # Array of blocks

{% for block in section.blocks %}
  {{ block.id }}
  {{ block.type }}
  {{ block.settings.title }}
  {{ block.shopify_attributes }}      # Required for theme editor
{% endfor %}
```

## Linklist (Menu) Object

```liquid
{% assign main_menu = linklists['main-menu'] %}

{% for link in main_menu.links %}
  <a href="{{ link.url }}" {% if link.active %}class="active"{% endif %}>
    {{ link.title }}
  </a>
  
  {% if link.links.size > 0 %}
    <ul>
      {% for child_link in link.links %}
        <a href="{{ child_link.url }}">{{ child_link.title }}</a>
      {% endfor %}
    </ul>
  {% endif %}
{% endfor %}
```

## Image Object

```liquid
{{ image.src }}
{{ image.alt }}
{{ image.width }}
{{ image.height }}
{{ image.aspect_ratio }}

{# Responsive images #}
{{
  image | image_url: width: 300 |
  image_tag:
    loading: 'lazy',
    sizes: '(min-width: 750px) 50vw, 100vw',
    widths: '300, 450, 600, 750, 900, 1200'
}}
```