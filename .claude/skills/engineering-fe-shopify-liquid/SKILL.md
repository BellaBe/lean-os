---
name: shopify-liquid
description: Shopify Liquid templating for themes and app extensions. Covers theme architecture, Liquid syntax, section schemas, app blocks, and Storefront API access. Triggers on: Shopify theme development, Liquid templates, theme sections, app blocks, theme app extensions, storefront customization.
---

# Shopify Liquid

Build Shopify themes and theme app extensions.

## Theme Architecture

```
theme/
├─ layout/
│   └─ theme.liquid              # Base layout wrapper
├─ templates/
│   ├─ index.json                # Homepage template
│   ├─ product.json              # Product page template
│   ├─ collection.json           # Collection page template
│   ├─ page.json                 # Custom page template
│   ├─ cart.json                 # Cart page template
│   ├─ blog.json                 # Blog listing template
│   ├─ article.json              # Blog post template
│   ├─ customers/
│   │   ├─ account.json
│   │   ├─ login.json
│   │   └─ order.json
│   └─ 404.json
├─ sections/
│   ├─ header.liquid
│   ├─ footer.liquid
│   ├─ featured-product.liquid
│   ├─ collection-list.liquid
│   └─ rich-text.liquid
├─ snippets/
│   ├─ product-card.liquid
│   ├─ price.liquid
│   └─ icon.liquid
├─ assets/
│   ├─ theme.css
│   └─ theme.js
├─ config/
│   └─ settings_schema.json      # Theme settings
└─ locales/
    ├─ en.default.json
    └─ fr.json
```

## Liquid Syntax

### Output

```liquid
{{ product.title }}
{{ product.price | money }}
{{ 'hello' | upcase }}
```

### Tags

```liquid
{% comment %} This is a comment {% endcomment %}

{% if product.available %}
  In stock
{% elsif product.inventory_quantity > 0 %}
  Low stock
{% else %}
  Sold out
{% endif %}

{% unless product.available %}
  Sold out
{% endunless %}

{% case product.type %}
  {% when 'Shirt' %}
    Clothing
  {% when 'Mug' %}
    Accessories
  {% else %}
    Other
{% endcase %}

{% for product in collection.products %}
  {{ product.title }}
  {% if forloop.first %}First item{% endif %}
  {% if forloop.last %}Last item{% endif %}
  {{ forloop.index }}      {# 1-indexed #}
  {{ forloop.index0 }}     {# 0-indexed #}
  {{ forloop.length }}     {# Total count #}
{% else %}
  No products found
{% endfor %}

{% for product in collection.products limit:4 offset:2 %}
  {{ product.title }}
{% endfor %}

{% for i in (1..5) %}
  {{ i }}
{% endfor %}

{% assign featured = collection.products.first %}
{% capture full_name %}{{ customer.first_name }} {{ customer.last_name }}{% endcapture %}

{% increment counter %}
{% decrement counter %}
```

### Common Filters

```liquid
{# String filters #}
{{ 'hello world' | capitalize }}        → Hello world
{{ 'hello world' | upcase }}            → HELLO WORLD
{{ 'HELLO' | downcase }}                → hello
{{ '  hello  ' | strip }}               → hello
{{ 'hello' | append: ' world' }}        → hello world
{{ 'hello world' | prepend: 'say ' }}   → say hello world
{{ 'hello' | replace: 'l', 'L' }}       → heLLo
{{ 'hello world' | split: ' ' }}        → ['hello', 'world']
{{ 'hello world' | truncate: 8 }}       → hello...
{{ 'hello world' | truncatewords: 1 }}  → hello...
{{ 'hello world' | remove: 'world' }}   → hello
{{ 'hello' | size }}                    → 5
{{ 'product-name' | handleize }}        → product-name
{{ 'Hello' | url_encode }}              → Hello
{{ '<p>Hi</p>' | strip_html }}          → Hi
{{ 'line1\nline2' | newline_to_br }}    → line1<br>line2
{{ text | escape }}                     → HTML escaped

{# Number filters #}
{{ 4.5 | ceil }}                        → 5
{{ 4.5 | floor }}                       → 4
{{ 4.5 | round }}                       → 5
{{ 1234 | plus: 5 }}                    → 1239
{{ 1234 | minus: 5 }}                   → 1229
{{ 10 | times: 2 }}                     → 20
{{ 10 | divided_by: 3 }}                → 3
{{ 10 | modulo: 3 }}                    → 1

{# Money filters #}
{{ product.price | money }}             → $10.00
{{ product.price | money_with_currency }} → $10.00 USD
{{ product.price | money_without_trailing_zeros }} → $10
{{ product.price | money_without_currency }} → 10.00

{# Date filters #}
{{ article.created_at | date: '%B %d, %Y' }}  → January 15, 2024
{{ 'now' | date: '%Y-%m-%d' }}                → 2024-01-15

{# Array filters #}
{{ collection.products | size }}
{{ collection.products | first }}
{{ collection.products | last }}
{{ collection.products | reverse }}
{{ collection.products | sort: 'title' }}
{{ collection.products | map: 'title' }}
{{ collection.products | where: 'available', true }}
{{ collection.products | concat: other_products }}
{{ array | join: ', ' }}
{{ array | uniq }}
{{ array | compact }}

{# URL filters #}
{{ 'product.jpg' | asset_url }}
{{ 'product.jpg' | asset_img_url: '300x300' }}
{{ product | img_url: '500x500' }}
{{ product.url | within: collection }}
{{ page.url | link_to: page.title }}
{{ 'products' | url_for_type }}
{{ 'products/my-product' | shopify_asset_url }}

{# Media filters #}
{{ product.featured_image | img_url: 'master' }}
{{ product.featured_image | image_tag }}
{{ image | image_url: width: 300, height: 300, crop: 'center' }}

{# JSON filters #}
{{ product | json }}
```

## JSON Templates

### Template Structure

```json
// templates/product.json
{
  "sections": {
    "main": {
      "type": "main-product",
      "settings": {
        "show_vendor": true
      }
    },
    "recommendations": {
      "type": "product-recommendations",
      "settings": {
        "heading": "You may also like"
      }
    }
  },
  "order": ["main", "recommendations"]
}
```

### Template with Dynamic Sections

```json
// templates/index.json
{
  "sections": {
    "slideshow": {
      "type": "slideshow",
      "blocks": {
        "slide1": {
          "type": "slide",
          "settings": {
            "image": "shopify://shop_images/hero.jpg",
            "heading": "Welcome"
          }
        }
      },
      "block_order": ["slide1"],
      "settings": {
        "autoplay": true
      }
    },
    "featured_collection": {
      "type": "featured-collection",
      "settings": {
        "collection": "frontpage"
      }
    }
  },
  "order": ["slideshow", "featured_collection"]
}
```

## Section Schema

### Basic Section

```liquid
{# sections/featured-product.liquid #}

<section class="featured-product">
  {% if section.settings.heading != blank %}
    <h2>{{ section.settings.heading }}</h2>
  {% endif %}
  
  {% assign product = section.settings.product %}
  {% if product %}
    <div class="product-card">
      <img src="{{ product.featured_image | img_url: '400x400' }}" alt="{{ product.title }}">
      <h3>{{ product.title }}</h3>
      <p>{{ product.price | money }}</p>
      <a href="{{ product.url }}">View Product</a>
    </div>
  {% else %}
    <p>Select a product in theme settings</p>
  {% endif %}
</section>

{% schema %}
{
  "name": "Featured Product",
  "tag": "section",
  "class": "section-featured-product",
  "settings": [
    {
      "type": "text",
      "id": "heading",
      "label": "Heading",
      "default": "Featured Product"
    },
    {
      "type": "product",
      "id": "product",
      "label": "Product"
    },
    {
      "type": "select",
      "id": "layout",
      "label": "Layout",
      "options": [
        { "value": "left", "label": "Image left" },
        { "value": "right", "label": "Image right" }
      ],
      "default": "left"
    }
  ],
  "presets": [
    {
      "name": "Featured Product"
    }
  ]
}
{% endschema %}
```

### Section with Blocks

```liquid
{# sections/slideshow.liquid #}

<div class="slideshow" data-autoplay="{{ section.settings.autoplay }}">
  {% for block in section.blocks %}
    <div class="slide" {{ block.shopify_attributes }}>
      {% case block.type %}
        {% when 'image' %}
          <img src="{{ block.settings.image | img_url: '1920x' }}" alt="{{ block.settings.alt }}">
          {% if block.settings.heading %}
            <h2>{{ block.settings.heading }}</h2>
          {% endif %}
          
        {% when 'video' %}
          <video src="{{ block.settings.video_url }}" autoplay muted loop></video>
      {% endcase %}
    </div>
  {% endfor %}
</div>

{% schema %}
{
  "name": "Slideshow",
  "tag": "section",
  "max_blocks": 5,
  "settings": [
    {
      "type": "checkbox",
      "id": "autoplay",
      "label": "Autoplay",
      "default": true
    },
    {
      "type": "range",
      "id": "speed",
      "label": "Slide duration",
      "min": 3,
      "max": 10,
      "step": 1,
      "unit": "s",
      "default": 5
    }
  ],
  "blocks": [
    {
      "type": "image",
      "name": "Image Slide",
      "settings": [
        {
          "type": "image_picker",
          "id": "image",
          "label": "Image"
        },
        {
          "type": "text",
          "id": "heading",
          "label": "Heading"
        },
        {
          "type": "text",
          "id": "alt",
          "label": "Image alt text"
        }
      ]
    },
    {
      "type": "video",
      "name": "Video Slide",
      "settings": [
        {
          "type": "video_url",
          "id": "video_url",
          "label": "Video URL",
          "accept": ["youtube", "vimeo"]
        }
      ]
    }
  ],
  "presets": [
    {
      "name": "Slideshow",
      "blocks": [
        { "type": "image" }
      ]
    }
  ]
}
{% endschema %}
```

## Schema Setting Types

```json
// Text inputs
{ "type": "text", "id": "heading", "label": "Heading", "default": "Hello" }
{ "type": "textarea", "id": "description", "label": "Description" }
{ "type": "richtext", "id": "content", "label": "Content" }
{ "type": "inline_richtext", "id": "title", "label": "Title" }
{ "type": "html", "id": "custom_html", "label": "Custom HTML" }

// Numbers
{ "type": "number", "id": "count", "label": "Count", "default": 4 }
{ "type": "range", "id": "opacity", "label": "Opacity", "min": 0, "max": 100, "step": 10, "unit": "%", "default": 100 }

// Boolean
{ "type": "checkbox", "id": "show_title", "label": "Show title", "default": true }

// Selection
{
  "type": "select",
  "id": "alignment",
  "label": "Alignment",
  "options": [
    { "value": "left", "label": "Left" },
    { "value": "center", "label": "Center" },
    { "value": "right", "label": "Right" }
  ],
  "default": "center"
}
{
  "type": "radio",
  "id": "size",
  "label": "Size",
  "options": [
    { "value": "small", "label": "Small" },
    { "value": "large", "label": "Large" }
  ],
  "default": "small"
}

// Resources
{ "type": "product", "id": "product", "label": "Product" }
{ "type": "collection", "id": "collection", "label": "Collection" }
{ "type": "blog", "id": "blog", "label": "Blog" }
{ "type": "article", "id": "article", "label": "Article" }
{ "type": "page", "id": "page", "label": "Page" }
{ "type": "link_list", "id": "menu", "label": "Menu" }

// Media
{ "type": "image_picker", "id": "image", "label": "Image" }
{ "type": "video", "id": "video", "label": "Video" }
{ "type": "video_url", "id": "video_url", "label": "Video URL", "accept": ["youtube", "vimeo"] }

// Appearance
{ "type": "color", "id": "text_color", "label": "Text color", "default": "#000000" }
{ "type": "color_background", "id": "background", "label": "Background" }
{ "type": "color_scheme", "id": "color_scheme", "label": "Color scheme" }
{ "type": "font_picker", "id": "heading_font", "label": "Heading font", "default": "helvetica_n4" }

// Other
{ "type": "url", "id": "link", "label": "Link" }
{ "type": "liquid", "id": "custom_liquid", "label": "Custom Liquid" }

// Spacing
{ "type": "header", "content": "Section Header" }
{ "type": "paragraph", "content": "Help text for merchants" }
```

## Theme App Extensions

### App Block Structure

```
extensions/
└─ theme-app-extension/
    ├─ blocks/
    │   └─ product-reviews.liquid
    ├─ snippets/
    │   └─ star-rating.liquid
    ├─ assets/
    │   ├─ reviews.css
    │   └─ reviews.js
    └─ locales/
        └─ en.default.json
```

### App Block

```liquid
{# extensions/theme-app-extension/blocks/product-reviews.liquid #}

{{ 'reviews.css' | asset_url | stylesheet_tag }}

<div class="app-reviews" data-product-id="{{ product.id }}">
  <h3>{{ block.settings.heading }}</h3>
  
  <div class="reviews-summary">
    {% render 'star-rating', rating: 4.5 %}
    <span>Based on {{ block.settings.review_count }} reviews</span>
  </div>
  
  <div class="reviews-list" id="reviews-{{ product.id }}">
    {# Reviews loaded via JavaScript #}
  </div>
</div>

<script src="{{ 'reviews.js' | asset_url }}" defer></script>

{% schema %}
{
  "name": "Product Reviews",
  "target": "section",
  "stylesheet": "reviews.css",
  "javascript": "reviews.js",
  "templates": ["product"],
  "settings": [
    {
      "type": "text",
      "id": "heading",
      "label": "Heading",
      "default": "Customer Reviews"
    },
    {
      "type": "number",
      "id": "review_count",
      "label": "Reviews to show",
      "default": 5
    }
  ]
}
{% endschema %}
```

### App Embed Block

```liquid
{# For blocks that can go anywhere (header, footer) #}

{% schema %}
{
  "name": "Chat Widget",
  "target": "body",
  "settings": [
    {
      "type": "text",
      "id": "welcome_message",
      "label": "Welcome message",
      "default": "How can we help?"
    }
  ]
}
{% endschema %}
```

## Storefront API Access

### Fetch Data in Liquid

```liquid
{# For theme app extensions, use App Proxy or fetch in JS #}

<script>
  async function fetchReviews(productId) {
    const response = await fetch(`/apps/my-app/reviews?product=${productId}`);
    const data = await response.json();
    return data;
  }
</script>
```

### App Proxy Pattern

```liquid
{# In app block #}
<div
  class="dynamic-content"
  data-endpoint="/apps/my-app/api/data"
  data-product="{{ product.id }}"
>
  <div class="loading">Loading...</div>
</div>

<script>
  document.querySelectorAll('.dynamic-content').forEach(async (el) => {
    const endpoint = el.dataset.endpoint;
    const productId = el.dataset.product;
    
    const response = await fetch(`${endpoint}?product=${productId}`);
    const html = await response.text();
    el.innerHTML = html;
  });
</script>
```

## Global Objects

### Core Objects

```liquid
{# Shop #}
{{ shop.name }}
{{ shop.email }}
{{ shop.domain }}
{{ shop.url }}
{{ shop.currency }}
{{ shop.money_format }}

{# Request/Page #}
{{ request.host }}
{{ request.path }}
{{ request.page_type }}
{{ template.name }}
{{ template.suffix }}

{# Customer (if logged in) #}
{% if customer %}
  {{ customer.email }}
  {{ customer.first_name }}
  {{ customer.orders_count }}
  {{ customer.total_spent | money }}
{% endif %}

{# Cart #}
{{ cart.item_count }}
{{ cart.total_price | money }}
{% for item in cart.items %}
  {{ item.product.title }}
  {{ item.quantity }}
  {{ item.line_price | money }}
{% endfor %}

{# Content #}
{{ content_for_header }}  {# Required in <head> #}
{{ content_for_layout }}  {# Required in <body> #}

{# Settings #}
{{ settings.color_primary }}
{{ settings.logo | img_url: '200x' }}
```

## References

- **Liquid objects**: See [references/objects.md](references/objects.md) for complete object reference
- **Filters**: See [references/filters.md](references/filters.md) for all Liquid filters
- **Integration**: Use `shopify-remix` skill for app backend that provides data to theme extensions