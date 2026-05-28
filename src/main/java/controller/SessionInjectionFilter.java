package controller;

import model.beans.*;

import javax.servlet.*;
import javax.servlet.annotation.WebFilter;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpSession;
import java.io.IOException;

@WebFilter(filterName = "SessionInjectionFilter", urlPatterns = "/*")
public class SessionInjectionFilter implements Filter {

    private boolean testMode = false;

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
        String envTestMode = System.getenv("ECO_TEST_MODE");
        if ("true".equalsIgnoreCase(envTestMode)) {
            testMode = true;
        }
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {
        if (testMode && request instanceof HttpServletRequest) {
            HttpServletRequest httpRequest = (HttpServletRequest) request;
            HttpSession session = httpRequest.getSession();

            // Inject mock user if not present
            if (session.getAttribute("user") == null) {
                Utente mockUser = new Utente();
                mockUser.setId(999);
                mockUser.setNome("EcoTest");
                mockUser.setCognome("User");
                mockUser.setEmail("ecotest@example.com");
                mockUser.setTelefono("1234567890");
                mockUser.setImmagine("logo.png");
                mockUser.setAdmin(true);

                // Create mock order
                Carrello orderCart = new Carrello();
                Prodotto orderProduct = new Prodotto();
                orderProduct.setId(101);
                orderProduct.setMarca("Apple");
                orderProduct.setModello("iPhone 13");
                orderProduct.setPrezzo(899.99);
                orderProduct.setPeso(0.2);
                orderProduct.setImmagine("logo.png");
                orderProduct.setQuantitaProdotto(5);
                orderProduct.setDescrizione("Apple iPhone 13 in excellent condition.");
                ProdottoCarrello orderItem = new ProdottoCarrello(orderProduct, 1);
                orderCart.aggiungiProdotto(orderItem);

                Ordine mockOrder = new Ordine();
                mockOrder.setId(1);
                mockOrder.setIndirizzo("Via Roma 1, Salerno");
                mockOrder.setPrezzoTotale(899.99);
                mockOrder.setUtente(mockUser);
                mockOrder.setCarrello(orderCart);

                java.util.ArrayList<Ordine> orders = new java.util.ArrayList<>();
                orders.add(mockOrder);
                mockUser.setOrdini(orders);

                // Create mock review
                Recensione mockReview = new Recensione(mockUser, orderProduct, 5, "Ottimo acquisto, velocissimo!", new java.util.Date());
                mockReview.setId(1);
                java.util.ArrayList<Recensione> reviews = new java.util.ArrayList<>();
                reviews.add(mockReview);
                mockUser.setRecensioni(reviews);

                session.setAttribute("user", mockUser);
            }

            // Inject mock carrello if not present, and populate with multiple mock products
            if (session.getAttribute("carrello") == null) {
                Carrello mockCart = new Carrello();
                
                Prodotto mockProduct1 = new Prodotto();
                mockProduct1.setId(100);
                mockProduct1.setMarca("Generic");
                mockProduct1.setModello("Heavy Item");
                mockProduct1.setPrezzo(199.99);
                mockProduct1.setPeso(2.5);
                mockProduct1.setImmagine("logo.png");
                mockProduct1.setQuantitaProdotto(10);
                mockProduct1.setDescrizione("This is a mock description for testing.");
                ProdottoCarrello item1 = new ProdottoCarrello(mockProduct1, 1);
                mockCart.aggiungiProdotto(item1);

                Prodotto mockProduct2 = new Prodotto();
                mockProduct2.setId(102);
                mockProduct2.setMarca("Samsung");
                mockProduct2.setModello("Galaxy S22");
                mockProduct2.setPrezzo(799.99);
                mockProduct2.setPeso(0.180);
                mockProduct2.setImmagine("logo.png");
                mockProduct2.setQuantitaProdotto(15);
                mockProduct2.setDescrizione("Galaxy S22 128GB version.");
                ProdottoCarrello item2 = new ProdottoCarrello(mockProduct2, 2);
                mockCart.aggiungiProdotto(item2);
                
                session.setAttribute("carrello", mockCart);
            }

            // Inject 50 mock products for grid views (showProdotti.jsp, index.jsp) to stress test DOM layout and lazy loading
            if (session.getAttribute("prodotti") == null) {
                java.util.ArrayList<Prodotto> productsList = new java.util.ArrayList<>();
                for (int i = 1; i <= 50; i++) {
                    Prodotto p = new Prodotto();
                    p.setId(200 + i);
                    p.setMarca("Brand" + i);
                    p.setModello("Mock Product Model " + i);
                    p.setPrezzo(49.99 + (i * 10));
                    p.setPeso(1.0 + (i * 0.1));
                    p.setImmagine("logo.png");
                    p.setQuantitaProdotto(20);
                    p.setDescrizione("This is the detailed mock description for mock product " + i + ".");
                    productsList.add(p);
                }
                session.setAttribute("prodotti", productsList);
            }

            // Inject categories for categories.jsp and index.jsp
            if (session.getAttribute("categorie") == null) {
                java.util.ArrayList<Categoria> categoriesList = new java.util.ArrayList<>();
                categoriesList.add(new Categoria("Smartphones"));
                categoriesList.add(new Categoria("Tablets"));
                categoriesList.add(new Categoria("Notebooks"));
                categoriesList.add(new Categoria("Accessories"));
                session.setAttribute("categorie", categoriesList);
            }

            // Inject wishlist for wishlist.jsp
            if (session.getAttribute("wishlist") == null) {
                WishList mockWishList = new WishList((Utente) session.getAttribute("user"));
                java.util.ArrayList<Prodotto> wishlistProducts = new java.util.ArrayList<>();
                for (int i = 1; i <= 6; i++) {
                    Prodotto p = new Prodotto();
                    p.setId(300 + i);
                    p.setMarca("WishBrand" + i);
                    p.setModello("Wish Product Model " + i);
                    p.setPrezzo(80.0 + (i * 5));
                    p.setPeso(0.5);
                    p.setImmagine("logo.png");
                    p.setQuantitaProdotto(5);
                    p.setDescrizione("Wishlist item number " + i);
                    wishlistProducts.add(p);
                }
                mockWishList.setProdotti(wishlistProducts);
                session.setAttribute("wishlist", mockWishList);
            }

            // Inject single product details for paginaProdotto.jsp
            if (session.getAttribute("prodotto") == null) {
                Prodotto singleProduct = new Prodotto();
                singleProduct.setId(100);
                singleProduct.setMarca("Apple");
                singleProduct.setModello("MacBook Pro 16");
                singleProduct.setPrezzo(2499.00);
                singleProduct.setPeso(2.1);
                singleProduct.setImmagine("logo.png");
                singleProduct.setQuantitaProdotto(3);
                singleProduct.setDescrizione("Supercharged by M2 Max, providing ultimate performance.");

                // Specifications
                java.util.ArrayList<Specifiche> specs = new java.util.ArrayList<>();
                specs.add(new Specifiche("Processore", "M2 Max"));
                specs.add(new Specifiche("RAM", "32GB"));
                specs.add(new Specifiche("Storage", "1TB SSD"));
                specs.add(new Specifiche("Schermo", "16.2 Liquid Retina XDR"));
                singleProduct.setSpecifiche(specs);

                // Reviews
                java.util.ArrayList<Recensione> prodReviews = new java.util.ArrayList<>();
                prodReviews.add(new Recensione((Utente) session.getAttribute("user"), singleProduct, 5, "Un mostro di potenza!", new java.util.Date()));
                prodReviews.add(new Recensione((Utente) session.getAttribute("user"), singleProduct, 4, "Bello ma un po' pesante.", new java.util.Date()));
                singleProduct.setRecensioni(prodReviews);

                session.setAttribute("prodotto", singleProduct);
                httpRequest.setAttribute("prodotto", singleProduct);
            }

            // Inject products for confronto (confronta.jsp)
            if (session.getAttribute("confronto1") == null) {
                Prodotto conf1 = (Prodotto) session.getAttribute("prodotto");
                session.setAttribute("confronto1", conf1);
            }
            if (session.getAttribute("confronto2") == null) {
                Prodotto conf2 = new Prodotto();
                conf2.setId(400);
                conf2.setMarca("Dell");
                conf2.setModello("XPS 15");
                conf2.setPrezzo(1899.00);
                conf2.setPeso(1.8);
                conf2.setImmagine("logo.png");
                conf2.setQuantitaProdotto(7);
                conf2.setDescrizione("Dell XPS 15 with Intel i7 and OLED display.");
                java.util.ArrayList<Specifiche> specs = new java.util.ArrayList<>();
                specs.add(new Specifiche("Processore", "Intel i7"));
                specs.add(new Specifiche("RAM", "16GB"));
                specs.add(new Specifiche("Storage", "512GB SSD"));
                specs.add(new Specifiche("Schermo", "15.6 OLED"));
                conf2.setSpecifiche(specs);
                session.setAttribute("confronto2", conf2);
            }
        }
        chain.doFilter(request, response);
    }

    @Override
    public void destroy() {
    }
}
