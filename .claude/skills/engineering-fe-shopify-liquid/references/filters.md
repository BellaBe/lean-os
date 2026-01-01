# Liquid Filters Reference

## Money Filters

```liquid
{{ product.price | money }}
→ $10.00

{{ product.price | money_with_currency }}
→ $10.00 USD

{{ product.price | money_without_currency }}
→ 10.00

{{ product.price | money_without_trailing_zeros }}
→ $10

{# Custom format #}
{{ 1000 | money_with_currency }}
→ $10.00 USD
```

## String Filters

```liquid
{# Case #}
{{ 'hello' | capitalize }}      → Hello
{{ 'hello' | upcase }}          → HELLO
{{ 'HELLO' | downcase }}        → hello

{# Whitespace #}
{{ '  hello  ' | strip }}       → hello
{{ '  hello  ' | lstrip }}      → hello  
{{ '  hello  ' | rstrip }}      →   hello
{{ 'hello\nworld' | strip_newlines }} → helloworld

{# Combine #}
{{ 'hello' | append: ' world' }}     → hello world
{{ 'world' | prepend: 'hello ' }}    → hello world
{{ 'hello' | repeat: 3 }}            → hellohellohello

{# Search & Replace #}
{{ 'hello world' | replace: 'world', 'there' }}     → hello there
{{ 'hello world world' | replace_first: 'world', 'there' }} → hello there world
{{ 'hello world' | remove: 'world' }}               → hello 
{{ 'hello world world' | remove_first: 'world' }}   → hello  world

{# Split & Join #}
{{ 'a,b,c' | split: ',' }}           → ['a', 'b', 'c']
{{ 'a,b,c' | split: ',' | join: '-' }} → a-b-c

{# Truncate #}
{{ 'hello world' | truncate: 8 }}           → hello...
{{ 'hello world' | truncate: 8, '!' }}      → hello w!
{{ 'hello world' | truncatewords: 1 }}      → hello...
{{ 'hello world' | truncatewords: 1, '!' }} → hello!

{# Size #}
{{ 'hello' | size }}             → 5
{{ collection.products | size }} → 10

{# Slice #}
{{ 'hello' | slice: 0 }}         → h
{{ 'hello' | slice: 1, 3 }}      → ell
{{ 'hello' | slice: -3, 3 }}     → llo

{# URL-safe #}
{{ 'Hello World!' | handleize }}     → hello-world
{{ 'Hello World!' | url_encode }}    → Hello%20World%21
{{ 'Hello%20World' | url_decode }}   → Hello World
{{ '/my path' | url_escape }}        → /my%20path
{{ '&<>' | escape }}                 → &amp;&lt;&gt;
{{ '&amp;' | escape_once }}          → &amp;

{# HTML #}
{{ '<p>Hello</p>' | strip_html }}    → Hello
{{ "line1\nline2" | newline_to_br }} → line1<br>line2

{# Defaults #}
{{ product.title | default: 'No title' }}
```

## Number Filters

```liquid
{# Rounding #}
{{ 4.6 | ceil }}         → 5
{{ 4.6 | floor }}        → 4
{{ 4.5 | round }}        → 5
{{ 4.5612 | round: 2 }}  → 4.56

{# Math #}
{{ 10 | plus: 5 }}       → 15
{{ 10 | minus: 5 }}      → 5
{{ 10 | times: 5 }}      → 50
{{ 10 | divided_by: 3 }} → 3
{{ 10 | modulo: 3 }}     → 1
{{ -5 | abs }}           → 5

{# At least/most #}
{{ 5 | at_least: 10 }}   → 10
{{ 15 | at_most: 10 }}   → 10
```

## Array Filters

```liquid
{# Access #}
{{ array | first }}
{{ array | last }}
{{ array | size }}

{# Transform #}
{{ array | reverse }}
{{ array | sort }}
{{ array | sort: 'title' }}
{{ array | sort_natural }}
{{ array | sort_natural: 'title' }}
{{ array | uniq }}
{{ array | compact }}               {# Remove nil values #}

{# Filter #}
{{ products | where: 'available', true }}
{{ products | where: 'type', 'Shirt' }}

{# Map (extract property) #}
{{ products | map: 'title' }}
→ ['Product 1', 'Product 2', ...]

{# Combine #}
{{ array1 | concat: array2 }}
{{ array | join: ', ' }}

{# Pagination #}
{% paginate collection.products by 12 %}
  {% for product in collection.products %}
    ...
  {% endfor %}
{% endpaginate %}
```

## Date Filters

```liquid
{{ article.created_at | date: '%B %d, %Y' }}
→ January 15, 2024

{{ 'now' | date: '%Y-%m-%d' }}
→ 2024-01-15

{{ article.created_at | date: '%I:%M %p' }}
→ 02:30 PM

{# Format codes #}
%a → Abbreviated weekday (Sun)
%A → Full weekday (Sunday)
%b → Abbreviated month (Jan)
%B → Full month (January)
%c → Preferred local date/time
%d → Day of month (01-31)
%e → Day of month (1-31)
%H → Hour 24h (00-23)
%I → Hour 12h (01-12)
%j → Day of year (001-366)
%m → Month (01-12)
%M → Minute (00-59)
%p → AM/PM
%S → Second (00-59)
%U → Week number, Sunday start
%W → Week number, Monday start
%w → Weekday (0-6, Sunday=0)
%x → Preferred date
%X → Preferred time
%y → Year 2-digit (24)
%Y → Year 4-digit (2024)
%Z → Timezone name
%% → Literal %
```

## URL Filters

```liquid
{# Asset URLs #}
{{ 'theme.css' | asset_url }}
{{ 'theme.js' | asset_url }}
{{ 'logo.png' | asset_url }}

{# External assets #}
{{ 'jquery.js' | shopify_asset_url }}
{{ '//cdn.example.com/file.js' | script_tag }}
{{ 'theme.css' | asset_url | stylesheet_tag }}

{# Image URLs #}
{{ product.featured_image | img_url: '500x500' }}
{{ product.featured_image | img_url: 'master' }}
{{ product.featured_image | img_url: '500x', crop: 'center' }}
{{ product.featured_image | img_url: 'x500' }}
{{ product.featured_image | product_img_url: '500x500' }}

{# Modern image_url filter #}
{{ image | image_url: width: 500 }}
{{ image | image_url: width: 500, height: 500, crop: 'center' }}

{# File URL #}
{{ 'example.pdf' | file_url }}
{{ 'example.mp4' | file_url }}

{# Links #}
{{ product.url | within: collection }}
{{ 'Contact Us' | link_to: '/pages/contact' }}
{{ 'Contact' | link_to: '/contact', class: 'nav-link', id: 'contact-link' }}
{{ tag | link_to_tag: tag }}
{{ tag | link_to_add_tag: tag }}
{{ tag | link_to_remove_tag: tag }}
{{ 'Shirts' | link_to_type }}
{{ 'Nike' | link_to_vendor }}

{# Payment icons #}
{{ shop.enabled_payment_types | payment_type_img_url }}
```

## Media Filters

```liquid
{# Image tag #}
{{ product.featured_image | image_url: width: 500 | image_tag }}
{{ product.featured_image | image_url: width: 500 | image_tag: 
    loading: 'lazy',
    class: 'product-image',
    alt: product.title
}}

{# Responsive images #}
{{
  product.featured_image |
  image_url: width: 1000 |
  image_tag:
    loading: 'lazy',
    sizes: '(min-width: 750px) 50vw, 100vw',
    widths: '300, 450, 600, 750, 900, 1000'
}}

{# Video #}
{{ product.media[0] | video_tag }}
{{ product.media[0] | video_tag: 
    autoplay: true, 
    loop: true, 
    muted: true,
    controls: false
}}

{# External video (YouTube, Vimeo) #}
{{ product.media[0] | external_video_tag }}
{{ product.media[0] | external_video_url }}

{# 3D Model #}
{{ product.media[0] | model_viewer_tag }}
{{ product.media[0] | model_viewer_tag:
    reveal: 'interaction',
    toggleable: true
}}

{# Media dimensions #}
{{ image | image_url: width: 500 }}
{{ image.width }}
{{ image.height }}
{{ image.aspect_ratio }}
```

## HTML Filters

```liquid
{# Tags #}
{{ 'theme.js' | asset_url | script_tag }}
→ <script src="//cdn.../theme.js"></script>

{{ 'theme.css' | asset_url | stylesheet_tag }}
→ <link href="//cdn.../theme.css" rel="stylesheet">

{{ product.featured_image | img_tag }}
→ <img src="..." alt="...">

{{ product.featured_image | img_tag: 'Alt text', 'css-class' }}

{# Form errors #}
{{ form.errors | default_errors }}
```

## Color Filters

```liquid
{{ '#FF0000' | color_to_rgb }}
→ rgb(255, 0, 0)

{{ '#FF0000' | color_to_hsl }}
→ hsl(0, 100%, 50%)

{{ 'rgb(255, 0, 0)' | color_to_hex }}
→ #ff0000

{{ '#FF0000' | color_brightness }}
→ 127.5 (0-255 scale)

{{ '#FF0000' | color_modify: 'alpha', 0.5 }}
→ rgba(255, 0, 0, 0.5)

{{ '#FF0000' | color_lighten: 20 }}
{{ '#FF0000' | color_darken: 20 }}
{{ '#FF0000' | color_saturate: 20 }}
{{ '#FF0000' | color_desaturate: 20 }}

{{ '#FF0000' | color_mix: '#0000FF', 50 }}
→ Mixes two colors

{{ '#FF0000' | color_contrast: '#FFFFFF' }}
→ Returns contrast ratio

{{ '#FF0000' | color_extract: 'red' }}
→ 255 (extract channel: red, green, blue, hue, saturation, lightness, alpha)
```

## JSON Filter

```liquid
{{ product | json }}
→ JSON representation

{# Use in JavaScript #}
<script>
  const product = {{ product | json }};
  const variants = {{ product.variants | json }};
</script>
```

## Metafield Filters

```liquid
{# Access metafield value #}
{{ product.metafields.custom.material.value }}

{# Metafield tag (renders appropriate HTML) #}
{{ product.metafields.custom.video | metafield_tag }}
{{ product.metafields.custom.image | metafield_tag }}

{# Metafield text #}
{{ product.metafields.custom.description | metafield_text }}
```

## Translation Filters

```liquid
{{ 'products.product.add_to_cart' | t }}
→ Add to cart (from locale file)

{{ 'products.product.price' | t: price: product.price | money }}
→ Price: $10.00

{# Pluralization #}
{{ 'cart.items' | t: count: cart.item_count }}
```

## Font Filters

```liquid
{{ settings.heading_font | font_face }}
{{ settings.heading_font | font_face: font_display: 'swap' }}

{{ settings.heading_font | font_url }}

{{ settings.heading_font | font_modify: 'weight', 'bold' }}
{{ settings.heading_font | font_modify: 'style', 'italic' }}
```

## Utility Filters

```liquid
{# Default value #}
{{ variable | default: 'fallback' }}
{{ nil | default: 'fallback' }}         → fallback
{{ false | default: 'fallback' }}       → false (not nil)
{{ '' | default: 'fallback' }}          → '' (not nil)

{# Allow false/empty to use default #}
{{ false | default: 'fallback', allow_false: true }} → fallback
{{ '' | default: 'fallback', allow_false: true }}   → fallback

{# Pluralize #}
{{ cart.item_count | pluralize: 'item', 'items' }}
→ 1 item / 2 items

{# Weight with unit #}
{{ product.variants.first.weight | weight_with_unit }}
→ 2 kg

{# Time tag #}
{{ article.created_at | time_tag }}
→ <time datetime="2024-01-15T10:30:00Z">January 15, 2024</time>

{{ article.created_at | time_tag: '%B %d' }}
→ <time datetime="...">January 15</time>

{# Highlight search terms #}
{{ product.title | highlight: search.terms }}
```

## Chaining Filters

```liquid
{# Multiple filters #}
{{ product.title | downcase | replace: ' ', '-' | truncate: 20 }}

{# Complex example #}
{{
  product.description |
  strip_html |
  truncatewords: 30 |
  escape
}}

{# Image with multiple options #}
{{
  product.featured_image |
  image_url: width: 800, height: 600, crop: 'center' |
  image_tag:
    loading: 'lazy',
    class: 'product-image',
    alt: product.title,
    sizes: '(min-width: 768px) 50vw, 100vw',
    widths: '400, 600, 800'
}}
```