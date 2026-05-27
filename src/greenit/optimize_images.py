import os
import pillow_avif
from PIL import Image

def resize_image_exact(src_path, dest_path, target_width, target_height):
    print(f"Resizing {os.path.basename(src_path)} to exact {target_width}x{target_height}...")
    with Image.open(src_path) as img:
        img_resized = img.resize((target_width, target_height), Image.Resampling.LANCZOS)
        img_resized.save(dest_path, format=img.format)

def resize_image_max_height(src_path, dest_path, target_height):
    with Image.open(src_path) as img:
        width, height = img.size
        # Preserve aspect ratio
        new_width = int(width * (target_height / height))
        print(f"Resizing {os.path.basename(src_path)} (from {width}x{height}) to height {target_height} -> {new_width}x{target_height}...")
        img_resized = img.resize((new_width, target_height), Image.Resampling.LANCZOS)
        img_resized.save(dest_path, format=img.format)

def main():
    upload_dir = r"c:\Users\aldom\Desktop\Projects\University of Salerno\2chance-dependability\upload"
    webapp_img_dir = r"c:\Users\aldom\Desktop\Projects\University of Salerno\2chance-dependability\src\main\webapp\img"

    # 1. Optimize Logo to exactly 82x58
    logo_upload_path = os.path.join(upload_dir, "logo.png")
    logo_webapp_path = os.path.join(webapp_img_dir, "logo.png")
    
    if os.path.exists(logo_upload_path):
        resize_image_exact(logo_upload_path, logo_upload_path, 82, 58)
    if os.path.exists(logo_webapp_path):
        resize_image_exact(logo_webapp_path, logo_webapp_path, 82, 58)

    # 2. Optimize Carousel images to exactly 710x388
    carousel_images = ["carosello1.webp", "carosello2.webp", "carosello3.webp"]
    for img_name in carousel_images:
        path = os.path.join(upload_dir, img_name)
        if os.path.exists(path):
            resize_image_exact(path, path, 710, 388)

    # 3. Optimize Product Images
    product_images = [
        "ipad8.jpg",
        "mackbookpro16.jpg",
        "iphone11.jpg",
        "iphone13promax.webp",
        "macbook-pro-2019.jpg",
        "ipadmini6.avif",
        "iphone13.avif"
    ]

    for img_name in product_images:
        path = os.path.join(upload_dir, img_name)
        if os.path.exists(path):
            # Create thumbnail with height exactly 49px (preserving aspect ratio)
            base, ext = os.path.splitext(img_name)
            thumb_name = f"{base}_thumb{ext}"
            thumb_path = os.path.join(upload_dir, thumb_name)
            
            # 3a. Generate thumbnail
            resize_image_max_height(path, thumb_path, 49)
            
            # 3b. Resize original to max height of 388px
            resize_image_max_height(path, path, 388)
        else:
            print(f"Product image not found: {img_name}")

if __name__ == "__main__":
    main()
