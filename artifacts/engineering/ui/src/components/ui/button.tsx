import * as React from "react"
import { Slot } from "@radix-ui/react-slot"
import { cva, type VariantProps } from "class-variance-authority"

import { cn } from "@/lib/utils"

const buttonVariants = cva(
  "inline-flex items-center justify-center gap-2 whitespace-nowrap rounded-md text-sm font-semibold transition-all disabled:pointer-events-none disabled:opacity-50 [&_svg]:pointer-events-none [&_svg:not([class*='size-'])]:size-4 shrink-0 [&_svg]:shrink-0 outline-none focus-visible:ring-[3px] aria-invalid:ring-destructive/20 dark:aria-invalid:ring-destructive/40 aria-invalid:border-destructive",
  {
    variants: {
      variant: {
        // Primary - solid brand background
        default: "bg-primary text-primary-foreground shadow-xs hover:bg-primary/90 focus-visible:ring-primary/20",
        // Secondary Color - brand border and light brand bg
        "secondary-color":
          "border border-[var(--color-brand-300)] bg-[var(--color-brand-50)] text-[var(--color-brand-700)] hover:bg-[var(--color-brand-100)] focus-visible:ring-primary/20",
        // Secondary Gray - gray border and white bg
        secondary:
          "border border-[var(--color-gray-300)] bg-background text-secondary-foreground shadow-xs hover:bg-[var(--color-gray-50)] focus-visible:ring-[var(--color-gray-100)]",
        // Tertiary Color - no border, brand text
        "tertiary-color":
          "text-[var(--color-brand-700)] hover:bg-[var(--color-brand-50)] focus-visible:ring-primary/20",
        // Tertiary Gray - no border, gray text (ghost)
        ghost:
          "text-secondary-foreground hover:bg-accent hover:text-accent-foreground dark:hover:bg-accent/50 focus-visible:ring-[var(--color-gray-100)]",
        // Destructive
        destructive:
          "bg-destructive text-white shadow-xs hover:bg-destructive/90 focus-visible:ring-destructive/20 dark:focus-visible:ring-destructive/40",
        // Outline (secondary-gray alias)
        outline:
          "border border-[var(--color-gray-300)] bg-background shadow-xs hover:bg-[var(--color-gray-50)] hover:text-accent-foreground dark:border-[var(--color-gray-600)] dark:hover:bg-[var(--color-gray-800)]",
        // Link Color
        link: "text-primary underline-offset-4 hover:underline hover:text-primary/80",
        // Link Gray
        "link-gray": "text-secondary-foreground underline-offset-4 hover:underline hover:text-foreground",
        // Success
        success:
          "bg-[var(--color-success-600)] text-white shadow-xs hover:bg-[var(--color-success-700)] focus-visible:ring-[var(--color-success-100)]",
        // Warning
        warning:
          "bg-[var(--color-warning-500)] text-white shadow-xs hover:bg-[var(--color-warning-600)] focus-visible:ring-[var(--color-warning-100)]",
      },
      size: {
        // sm: 36px height, 12px padding, 4px gap
        sm: "h-9 px-3 py-2 gap-1 text-sm has-[>svg]:px-2.5",
        // md: 40px height, 16px padding, 8px gap
        default: "h-10 px-4 py-2.5 gap-2 text-sm has-[>svg]:px-3.5",
        // lg: 44px height, 20px padding, 8px gap
        lg: "h-11 px-5 py-2.5 gap-2 text-base has-[>svg]:px-4",
        // xl: 48px height, 20px padding, 8px gap
        xl: "h-12 px-5 py-3 gap-2 text-base has-[>svg]:px-4",
        // 2xl: 60px height, 32px padding, 12px gap
        "2xl": "h-[60px] px-8 py-4 gap-3 text-lg has-[>svg]:px-6 [&_svg:not([class*='size-'])]:size-5",
        // Icon sizes
        icon: "size-10",
        "icon-sm": "size-9",
        "icon-lg": "size-11",
        "icon-xl": "size-12",
      },
    },
    defaultVariants: {
      variant: "default",
      size: "default",
    },
  }
)

function Button({
  className,
  variant = "default",
  size = "default",
  asChild = false,
  ...props
}: React.ComponentProps<"button"> &
  VariantProps<typeof buttonVariants> & {
    asChild?: boolean
  }) {
  const Comp = asChild ? Slot : "button"

  return (
    <Comp
      data-slot="button"
      data-variant={variant}
      data-size={size}
      className={cn(buttonVariants({ variant, size, className }))}
      {...props}
    />
  )
}

export { Button, buttonVariants }
