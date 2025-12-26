import * as React from "react"
import { Slot } from "@radix-ui/react-slot"
import { cva, type VariantProps } from "class-variance-authority"

import { cn } from "@/lib/utils"

const badgeVariants = cva(
  "inline-flex items-center justify-center rounded-full border px-2.5 py-0.5 text-xs font-medium w-fit whitespace-nowrap shrink-0 [&>svg]:size-3 gap-1.5 [&>svg]:pointer-events-none focus-visible:border-ring focus-visible:ring-ring/50 focus-visible:ring-[3px] aria-invalid:ring-destructive/20 dark:aria-invalid:ring-destructive/40 aria-invalid:border-destructive transition-[color,box-shadow] overflow-hidden",
  {
    variants: {
      variant: {
        // Brand/Primary - purple
        default:
          "border-transparent bg-primary text-primary-foreground [a&]:hover:bg-primary/90",
        // Gray/Secondary
        secondary:
          "border-[var(--color-gray-200)] bg-[var(--color-gray-50)] text-[var(--color-gray-700)] [a&]:hover:bg-[var(--color-gray-100)]",
        // Error/Destructive - red
        destructive:
          "border-transparent bg-[var(--color-error-50)] text-[var(--color-error-700)] [a&]:hover:bg-[var(--color-error-100)]",
        // Success - green
        success:
          "border-transparent bg-[var(--color-success-50)] text-[var(--color-success-700)] [a&]:hover:bg-[var(--color-success-100)]",
        // Warning - orange/amber
        warning:
          "border-transparent bg-[var(--color-warning-50)] text-[var(--color-warning-700)] [a&]:hover:bg-[var(--color-warning-100)]",
        // Info - blue
        info:
          "border-transparent bg-[var(--color-blue-50)] text-[var(--color-blue-700)] [a&]:hover:bg-[var(--color-blue-100)]",
        // Purple (brand color)
        purple:
          "border-transparent bg-[var(--color-brand-50)] text-[var(--color-brand-700)] [a&]:hover:bg-[var(--color-brand-100)]",
        // Outline
        outline:
          "border-[var(--color-gray-300)] dark:border-[var(--color-gray-700)] bg-transparent text-[var(--color-gray-700)] dark:text-[var(--color-gray-300)] [a&]:hover:bg-[var(--color-gray-50)] dark:[a&]:hover:bg-[var(--color-gray-800)]",
        // Solid variants for stronger emphasis
        "destructive-solid":
          "border-transparent bg-[var(--color-error-600)] text-white [a&]:hover:bg-[var(--color-error-700)]",
        "success-solid":
          "border-transparent bg-[var(--color-success-600)] text-white [a&]:hover:bg-[var(--color-success-700)]",
        "warning-solid":
          "border-transparent bg-[var(--color-warning-500)] text-white [a&]:hover:bg-[var(--color-warning-600)]",
        "info-solid":
          "border-transparent bg-[var(--color-blue-600)] text-white [a&]:hover:bg-[var(--color-blue-700)]",
      },
      size: {
        sm: "px-2 py-0.5 text-xs",
        default: "px-2.5 py-0.5 text-xs",
        lg: "px-3 py-1 text-sm",
      },
    },
    defaultVariants: {
      variant: "default",
      size: "default",
    },
  }
)

function Badge({
  className,
  variant,
  size,
  asChild = false,
  ...props
}: React.ComponentProps<"span"> &
  VariantProps<typeof badgeVariants> & { asChild?: boolean }) {
  const Comp = asChild ? Slot : "span"

  return (
    <Comp
      data-slot="badge"
      data-variant={variant}
      data-size={size}
      className={cn(badgeVariants({ variant, size }), className)}
      {...props}
    />
  )
}

export { Badge, badgeVariants }
