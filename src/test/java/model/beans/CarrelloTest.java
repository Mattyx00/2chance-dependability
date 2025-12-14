package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Carrello class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Constructor initialization
 * - getTotaleCarrello() with empty/single/multiple items
 * - aggiungiProdotto() with null checks and various cart states
 * - eliminaProdotto() with null checks, empty cart, existing/non-existing
 * products
 * - cambiaQuantita() with null/invalid inputs and state exceptions
 */
@DisplayName("Carrello Tests")
class CarrelloTest {

    private Carrello cart;

    @BeforeEach
    void setUp() {
        cart = new Carrello();
    }

    // ========================================================================
    // Constructor Tests: Carrello()
    // ========================================================================

    @Test
    @DisplayName("Constructor should initialize empty non-null product list")
    void shouldInitializeEmptyNonNullProductListWhenConstructed() {
        // Assert
        assertNotNull(cart, "Carrello instance should be created");
        assertNotNull(cart.getProdotti(), "Product list should not be null");
        assertTrue(cart.getProdotti().isEmpty(), "Product list should be empty");
        assertEquals(0, cart.getProdotti().size(), "Product list size should be 0");
    }

    // ========================================================================
    // getTotaleCarrello() Tests
    // ========================================================================

    @Test
    @DisplayName("getTotaleCarrello should return zero for empty cart")
    void shouldReturnZeroForEmptyCart() {
        // Act
        double totalCartProductsCost = cart.getTotaleCarrello();

        // Assert
        assertEquals(0.0, totalCartProductsCost, 0.001, "Empty cart should have zero total");
    }

    @Test
    @DisplayName("getTotaleCarrello should calculate correct total for single item")
    void shouldCalculateCorrectTotalForSingleItem() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 2); // total = 20.0
        cart.aggiungiProdotto(productCart);

        // Act
        double totalCartProductsCost = cart.getTotaleCarrello();

        // Assert
        assertEquals(20.0, totalCartProductsCost, 0.001, "Cart total should be 20.0 (10.0 * 2)");
    }

    @Test
    @DisplayName("getTotaleCarrello should calculate correct total for multiple items")
    void shouldCalculateCorrectTotalForMultipleItems() {
        // Arrange
        Prodotto product1 = createProduct(1, "Product1", 10.0);
        Prodotto product2 = createProduct(2, "Product2", 7.75);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product1, 2);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product2, 2);
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Act
        double totalCartProductsCost = cart.getTotaleCarrello();

        // Assert
        assertEquals(35.5, totalCartProductsCost, 0.01, "Cart total should be 35.5 (20.0 + 15.5)");
    }

    @Test
    @DisplayName("getTotaleCarrello should handle items with zero price")
    void shouldCalculateTotalWithZeroPriceItems() {
        // Arrange
        Prodotto product1 = createProduct(1, "FreeProduct", 0.0);
        Prodotto product2 = createProduct(2, "PaidProduct", 10.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product1, 5);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product2, 3);
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Act
        double totalCartProductsCost = cart.getTotaleCarrello();

        // Assert
        assertEquals(30.0, totalCartProductsCost, 0.001, "Cart total should be 30.0 (0.0 + 30.0)");
    }

    // ========================================================================
    // aggiungiProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("aggiungiProdotto should throw exception when adding null product")
    void shouldThrowExceptionWhenAddingNullProduct() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> cart.aggiungiProdotto(null),
                "Should throw IllegalArgumentException when adding null");
        assertTrue(exception.getMessage().contains(
                "prodotto da aggiungere non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("aggiungiProdotto should add product to empty cart")
    void shouldAddProductToEmptyCart() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 2);

        // Act
        boolean result = cart.aggiungiProdotto(productCart);

        // Assert
        assertTrue(result, "aggiungiProdotto should return true");
        assertEquals(1, cart.getProdotti().size(), "Cart should have 1 item");
        assertTrue(cart.getProdotti().contains(productCart), "Cart should contain the added product");
    }

    @Test
    @DisplayName("aggiungiProdotto should add multiple different products to cart")
    void shouldAddMultipleProductsToCart() {
        // Arrange
        Prodotto product1 = createProduct(1, "Product1", 10.0);
        Prodotto product2 = createProduct(2, "Product2", 15.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product1, 2);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product2, 1);

        // Act
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Assert
        assertEquals(2, cart.getProdotti().size(), "Cart should have 2 items");
        assertTrue(cart.getProdotti().contains(productCart1), "Cart should contain first product");
        assertTrue(cart.getProdotti().contains(productCart2), "Cart should contain second product");
    }

    @Test
    @DisplayName("aggiungiProdotto should allow adding duplicate product (same ID)")
    void shouldAllowAddingDuplicateProduct() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product, 2);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product, 3);

        // Act
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Assert
        assertEquals(2, cart.getProdotti().size(),
                "Cart should allow duplicate products (ArrayList behavior)");
        assertTrue(cart.getProdotti().contains(productCart1),
                "Cart should contain first product");
        assertTrue(cart.getProdotti().contains(productCart2),
                "Cart should contain second product");
    }

    // ========================================================================
    // eliminaProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("eliminaProdotto should throw exception when removing null product")
    void shouldThrowExceptionWhenRemovingNullProduct() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> cart.eliminaProdotto(null),
                "Should throw IllegalArgumentException when removing null");
        assertTrue(
                exception.getMessage().contains("prodotto da eliminare non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("eliminaProdotto should do nothing when removing from empty cart")
    void shouldDoNothingWhenRemovingFromEmptyCart() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);

        // Act
        cart.eliminaProdotto(product);

        // Assert
        assertTrue(cart.getProdotti().isEmpty(), "Cart should remain empty");
        assertEquals(0, cart.getProdotti().size(), "Cart size should be 0");
    }

    @Test
    @DisplayName("eliminaProdotto should remove existing product from cart")
    void shouldRemoveExistingProductFromCart() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 2);
        cart.aggiungiProdotto(productCart);

        // Act
        cart.eliminaProdotto(product);

        // Assert
        assertTrue(cart.getProdotti().isEmpty(), "Cart should be empty after removal");
        assertEquals(0, cart.getProdotti().size(), "Cart size should be 0");
    }

    @Test
    @DisplayName("eliminaProdotto should do nothing when product not in cart")
    void shouldDoNothingWhenRemovingNonExistingProduct() {
        // Arrange
        Prodotto product1 = createProduct(1, "Product1", 10.0);
        Prodotto product2 = createProduct(2, "Product2", 15.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product1, 2);
        cart.aggiungiProdotto(productCart1);

        // Act
        cart.eliminaProdotto(product2);

        // Assert
        assertEquals(1, cart.getProdotti().size(), "Cart should still have 1 item");
        assertTrue(cart.getProdotti().contains(productCart1), "Original product should remain");
    }

    @Test
    @DisplayName("eliminaProdotto should remove all matching products by ID")
    void shouldRemoveAllMatchingProductsByIdFromCart() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product, 2);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product, 3);
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Act
        cart.eliminaProdotto(product);

        // Assert
        assertTrue(
                cart.getProdotti().isEmpty(),
                "All products with matching ID should be removed");
    }

    @Test
    @DisplayName("eliminaProdotto should only remove products with matching ID")
    void shouldRemoveOnlyMatchingProducts() {
        // Arrange
        Prodotto product1 = createProduct(1, "Product1", 10.0);
        Prodotto product2 = createProduct(2, "Product2", 15.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product1, 2);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product2, 1);
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Act
        cart.eliminaProdotto(product1);

        // Assert
        assertEquals(1, cart.getProdotti().size(), "Cart should have 1 item");
        assertEquals(product2.getId(), cart.getProdotti().get(0).getProdotto().getId(),
                "Remaining product should be product2");
    }

    // ========================================================================
    // cambiaQuantita() Tests
    // ========================================================================

    @Test
    @DisplayName("cambiaQuantita should throw exception when product is null")
    void shouldThrowExceptionWhenChangingQuantityWithNullProduct() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> cart.cambiaQuantita(null, 5),
                "Should throw IllegalArgumentException for null product");
        assertTrue(exception.getMessage().contains("prodotto non può essere null"),
                "Exception message should mention null product");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception when quantity is zero")
    void shouldThrowExceptionWhenChangingQuantityToZero() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 2);
        cart.aggiungiProdotto(productCart);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> cart.cambiaQuantita(product, 0),
                "Should throw IllegalArgumentException for zero quantity");
        assertTrue(exception.getMessage().contains("quantità deve essere maggiore di zero"),
                "Exception message should mention zero quantity");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception when quantity is negative")
    void shouldThrowExceptionWhenChangingQuantityToNegative() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 2);
        cart.aggiungiProdotto(productCart);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> cart.cambiaQuantita(product, -1),
                "Should throw IllegalArgumentException for negative quantity");
        assertTrue(exception.getMessage().contains("quantità deve essere maggiore di zero"),
                "Exception message should mention quantity requirement");
    }

    @Test
    @DisplayName("cambiaQuantita should update quantity for existing product")
    void shouldUpdateQuantityForExistingProduct() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 2);
        cart.aggiungiProdotto(productCart);

        // Act
        cart.cambiaQuantita(product, 10);

        // Assert
        assertEquals(1, cart.getProdotti().size(), "Cart should still have 1 item");
        assertEquals(10, cart.getProdotti().get(0).getQuantita(),
                "Product quantity should be updated to 10");
    }

    @Test
    @DisplayName("cambiaQuantita should update quantity to 1 (minimum valid)")
    void shouldUpdateQuantityToMinimumValid() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 5);
        cart.aggiungiProdotto(productCart);

        // Act
        cart.cambiaQuantita(product, 1);

        // Assert
        assertEquals(1, cart.getProdotti().get(0).getQuantita(),
                "Product quantity should be updated to 1");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception when product not in cart")
    void shouldThrowExceptionWhenChangingQuantityOfNonExistingProduct() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart = new ProdottoCarrello(product, 5);
        cart.aggiungiProdotto(productCart);

        Prodotto productNotAdded = createProduct(2, "Product2", 20.0);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> cart.cambiaQuantita(productNotAdded, 10),
                "Should throw IllegalStateException when product not in cart");
        assertTrue(exception.getMessage().contains("non è presente nel carrello"),
                "Exception message should mention product not in cart");
        assertTrue(exception.getMessage().contains("" + productNotAdded.getId()),
                "Exception message should mention product ID");
    }

    @Test
    @DisplayName("cambiaQuantita should throw exception for empty cart")
    void shouldThrowExceptionWhenChangingQuantityInEmptyCart() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> cart.cambiaQuantita(product, 5),
                "Should throw IllegalStateException for empty cart");
        assertTrue(exception.getMessage().contains("non è presente nel carrello"),
                "Exception message should indicate product not found");
    }

    @Test
    @DisplayName("cambiaQuantita should update only first matching product when duplicates exist")
    void shouldUpdateFirstMatchingProductWhenDuplicatesExist() {
        // Arrange
        Prodotto product = createProduct(1, "Product1", 10.0);
        ProdottoCarrello productCart1 = new ProdottoCarrello(product, 2);
        ProdottoCarrello productCart2 = new ProdottoCarrello(product, 3);
        cart.aggiungiProdotto(productCart1);
        cart.aggiungiProdotto(productCart2);

        // Act
        cart.cambiaQuantita(product, 10);

        // Assert
        assertEquals(2, cart.getProdotti().size(), "Cart should still have 2 items");
        assertEquals(10, cart.getProdotti().get(0).getQuantita(),
                "First product quantity should be updated to 10");
        assertEquals(3, cart.getProdotti().get(1).getQuantita(),
                "Second product quantity should remain 3");
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    /**
     * Helper method to create a Prodotto instance for testing.
     */
    private Prodotto createProduct(int id, String modello, double prezzo) {
        Prodotto product = new Prodotto();
        product.setId(id);
        product.setModello(modello);
        product.setMarca("TestMarca");
        product.setDescrizione("Test Description");
        product.setPrezzo(prezzo);
        product.setPeso(1.0);
        product.setQuantitaProdotto(10);
        return product;
    }
}
